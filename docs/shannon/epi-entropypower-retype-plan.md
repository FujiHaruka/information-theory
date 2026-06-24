# EPI 無条件化: entropyPower 二層定義 + coercion bridge サブ計画 (S1)

> **Parent**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) §Phase 1 (柱 1)
> **slug**: `epi-entropypower-retype-plan` (`@residual(plan:epi-entropypower-retype-plan)` と一致)
> **入力 inventory**: [`epi-uncond-entropypower-retype-inventory.md`](epi-uncond-entropypower-retype-inventory.md) (Phase 0-A/0-C、API 在庫 + skeleton 確定済)

<!--
記法は親 plan / moonshot-template に揃える:
状態絵文字 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更(判断ログ参照)。
取り消し線 = 廃止 step (履歴のため残す)。判断ログ append-only。
rg "^- \[ \]" で残 step 横断 grep、rg "🔄" でピボット箇所だけ拾える。
-->

## 進捗

- [ ] Phase A — skeleton 配置 (新 file + 2 def + 3 bridge sorry、type-check done) 📋
- [ ] Phase B — coercion bridge 群 genuine 化 (ac / singular / dirac) 📋
- [ ] Phase C — 非自明値 sanity gate (gaussianReal a.c. ≠ 0 / dirac 特異 = 0) 📋
- [ ] Phase D — 旧 Real `entropyPower` の退避判断 + `InformationTheory.lean` 編入 📋

proof-log: yes (`docs/shannon/proof-log-epi-entropypower-retype.md`、Phase B 完了時に着手 / Phase D 完了時に締め)。

---

## ゴール / Approach

親 plan §Phase 1 (柱 1) を受けて、退化トラップ (特異測度 → 旧 `entropyPower = exp 0 = 1`) を
**再型付けで除去する二層定義**を導入し、a.c. 枝で既存 Real workhorse と一致することを保証する
coercion bridge を完成させる。本 sub-plan の成果物は新 file 1 本 + 定義 2 本 + bridge ~4–6 本。

### Approach (解の全体形)

#### 二層定義の shape (非分岐 entropyPower、case-split を EReal 側に一元化)

inventory で確定した shape を採用する (verbatim 確認済の Mathlib API に直結):

- **(a) Real workhorse は温存・不変**: `differentialEntropy : Measure ℝ → ℝ`
  (`DifferentialEntropy.lean:45`)。本 sub-plan では **触らない** (改名もしない、第一候補)。
  既存 genuine 資産 (de Bruijn `HasDerivAt` / Stam / AWGN) の主役。
- **(b1) `differentialEntropyExt : Measure ℝ → EReal`**: 特異で `⊥`、a.c. で `↑(differentialEntropy μ)`。
  `open Classical in` + `irreducible_def` + `if μ ≪ volume then ↑(differentialEntropy μ) else ⊥`。
  case-split (特異/a.c.) は **この EReal 値の側に一元化**する。
- **(b2) `entropyPowerExt : Measure ℝ → ℝ≥0∞`**: **非分岐** `EReal.exp (2 * differentialEntropyExt μ)`。
  case-split を持たない。`EReal.exp` が特異枝・a.c. 枝の両方を 1 関数で吸収する:
  - 特異 `differentialEntropyExt μ = ⊥` ⟹ `2 * ⊥ = ⊥` ⟹ `EReal.exp ⊥ = 0` (退化トラップ除去)。
  - a.c. `differentialEntropyExt μ = ↑h` ⟹ `2 * ↑h = ↑(2h)` ⟹ `EReal.exp ↑(2h) = ENNReal.ofReal (Real.exp (2h))` (Real workhorse と一致)。

非分岐定義の理由 (Mathlib-shape-driven): EPI 主定理の lift は `EReal.exp_monotone` [gcongr]
(`ERealExp.lean:72`) で `differentialEntropyExt` レベルの不等式を直接 `entropyPowerExt` の
不等式に持ち上げられる。RHS の和は **`entropyPowerExt X + entropyPowerExt Y` を ℝ≥0∞ 上で取る**
(EReal 上で `h(X)+h(Y)` を足してから exp するのではない) — これにより混合 case で `⊥` が和を
吸収して RHS が `0` に潰れる事故 (inventory §主要前提ボックス `add_bot`/`bot_add`) を構造的に回避する。
RHS は主定理 statement (親 plan §1) が既に ℝ≥0∞ 加算で書かれているため自動回避。

#### a.c. 判定の definitional 化 (klDiv precedent)

`Decidable (μ ≪ volume)` は Mathlib 不在 (loogle Found 0) だが、Mathlib `klDiv`
(`KullbackLeibler/Basic.lean:55-58`、verbatim 確認: `open Classical in` +
`noncomputable irreducible_def` + `if μ ≪ ν ∧ ... then ... else ∞`) が同型 pattern を実運用している。
これを precedent に `differentialEntropyExt` も `open Classical in` で `Classical.propDecidable`
を供給 + `irreducible_def` で downstream の意図しない unfold / `simp`/`rfl` on `if` 汚染を防ぐ。
downstream reasoning は `differentialEntropyExt_of_ac` / `_of_singular` 展開 lemma 経由
(klDiv の `klDiv_of_ac_of_integrable` 同様)。`μ : Measure ℝ` `[IsProbabilityMeasure μ]` +
`volume` SigmaFinite ⟹ `haveLebesgueDecomposition_of_sigmaFinite` (priority 100 instance) が
HLD を自動 resolve するため、特異/a.c. 判定に追加 instance hyp は不要。

#### coercion bridge の対象 lemma 群 (consumer 結論形に合わせて確定)

S2 (downstream re-port) / S3 (singular-mixed) / case1 (a.c. core) の想定 consumer が要求する
結論形に合わせて bridge を用意する:

| bridge lemma | 結論形 | 想定 consumer |
|---|---|---|
| `entropyPowerExt_of_ac` | `μ ≪ volume → entropyPowerExt μ = ENNReal.ofReal (Real.exp (2 * differentialEntropy μ))` | case1 a.c. core (`ENNReal.ofReal_le_ofReal` lift)、S2 等式書換 |
| `entropyPowerExt_singular` | `¬ μ ≪ volume → entropyPowerExt μ = 0` | S3 case2/3 (RHS の特異項 → 0)、混合 case の `N(Y)=0` |
| `differentialEntropyExt_of_ac` | `μ ≪ volume → differentialEntropyExt μ = ↑(differentialEntropy μ)` | EReal レベルの不等式 lift (`EReal.coe_add` 和保存) |
| `differentialEntropyExt_singular` | `¬ μ ≪ volume → differentialEntropyExt μ = ⊥` | 特異判定の展開 |
| `entropyPowerExt_dirac` | `entropyPowerExt (Measure.dirac m) = 0` | sanity gate (退化トラップ除去の verbatim 検証) |
| `entropyPowerExt_gaussianReal` | `v ≠ 0 → entropyPowerExt (gaussianReal m v) = ENNReal.ofReal (2πe·v)` | sanity gate (a.c. 非自明値 ≠ 0) |

**Mathlib-shape-driven の確定根拠** (consumer 結論形 ⊢ 定義 shape): a.c. consumer は
`ENNReal.ofReal_le_ofReal` (`ENNReal/Real.lean:137`) + `ENNReal.ofReal_add` (`:52`、両 nonneg 前提
verbatim) で Real EPI を ℝ≥0∞ に持ち上げる。よって a.c. 枝の `entropyPowerExt` は
**`ENNReal.ofReal (Real.exp (...))` 形 verbatim** で取り出せる必要があり、`EReal.exp_coe`
(`ERealExp.lean:45`、`exp ↑x = ENNReal.ofReal (Real.exp x)`、`rfl`) がこの形を直接供給する。
EReal レベルの単調 lift は `EReal.exp_monotone` を使う consumer に `differentialEntropyExt_of_ac`
+ `EReal.coe_add` (`EReal/Basic.lean:301`、和保存 `rfl`) を渡す。

#### `def` RHS が詰まった場合の対処順序 (CLAUDE.md「sorry を書けない箇所」)

`differentialEntropyExt` / `entropyPowerExt` は `def` のため RHS に `sorry` を書けない。詰まったら:

1. **第一選択 — 結論形に合わせた定義書換**: EReal.exp 非分岐定義が `EReal.mul` 挙動等で組めない場合、
   `entropyPowerExt μ := if μ ≪ volume then ENNReal.ofReal (Real.exp (2*differentialEntropy μ)) else 0`
   の **ℝ≥0∞ 直接 case-split 定義**へ書換 (EReal 算術を完全回避、`if_pos`/`if_neg` + `ENNReal.ofReal`
   のみで bridge が組める)。これは L-Uncond-0-δ の退避先と同一 (下記 Phase A 撤退ライン)。
   bridge 補題 (proof body) は `sorry` + `@residual(plan:epi-entropypower-retype-plan)` で抜ける。
2. **第二選択 (暫定)** — 当該セッションで定義書換が無理な場合に限り、signature を defect 形のまま残し
   docstring に `@audit:defect(<kind>)` + `@audit:closed-by-successor(epi-unconditional-moonshot-plan)`
   + 「なぜ第一選択が無理だったか」1 行を併記。tier 5 暫定マーカー、stable resting state ではない。

**禁止** (CLAUDE.md 検証の誠実性): `Prop := True` placeholder / 結論型≡仮説型 `:= h` 循環 /
load-bearing `*Hypothesis` predicate に核を bundle / 退化定義悪用 (特異 → `⊥`/`0` は真の値なので
OK だが、a.c. 判定を常時 false に倒して LHS を `0` に潰すのは退化定義悪用 — Phase C sanity gate で検出)。

---

## Phase A — skeleton 配置 (type-check done) 📋

proof-log: no (skeleton のみ)。

新 file **`InformationTheory/Shannon/EntropyPowerExt.lean`** を作る (inventory §着手 skeleton を base に)。
import は pinpoint (`import Mathlib` 禁止):

- `InformationTheory.Shannon.DifferentialEntropy` (Real workhorse + `differentialEntropy_dirac`)
- `Mathlib.Analysis.SpecialFunctions.Log.ERealExp` (`EReal.exp` 群)
- `Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue` (a.c./特異判定、HLD instance)
- `Mathlib.Data.EReal.Basic` (`EReal.coe_add` / `coe_mul` / `toENNReal` 系)
- `Mathlib.Data.EReal.Operations` (`mul_bot_of_pos` / `coe_mul_bot_of_pos`、L-Uncond-0-δ 確認用)

steps:

- [ ] `differentialEntropyExt : Measure ℝ → EReal` を `open Classical in` + `noncomputable irreducible_def`
      + `if μ ≪ volume then (differentialEntropy μ : EReal) else ⊥` で配置 (klDiv precedent)。
- [ ] `entropyPowerExt : Measure ℝ → ℝ≥0∞` を `noncomputable def ... := EReal.exp (2 * differentialEntropyExt μ)`
      で配置 (非分岐)。
- [ ] bridge 4 本 + sanity 2 本を `:= by sorry` (各 `-- @residual(plan:epi-entropypower-retype-plan)`) で配置:
      `differentialEntropyExt_of_ac` / `_singular` / `entropyPowerExt_of_ac` / `_singular` /
      `entropyPowerExt_dirac` / `entropyPowerExt_gaussianReal`。
- [ ] verify: `lake env lean InformationTheory/Shannon/EntropyPowerExt.lean` が 0 errors
      (sorry warning のみ許容)。type-check done で commit 可。

### Phase A 撤退ライン

- **L-Uncond-0-δ** (親 plan + inventory 由来、最有力): `EReal.mul` の `2 * ⊥` / `(2:EReal) * ↑x` 挙動が
  非分岐定義で想定外 → ℝ≥0∞ 直接 case-split 定義
  `if μ ≪ volume then ENNReal.ofReal (Real.exp (2*differentialEntropy μ)) else 0` に切替。
  **verbatim 確認済の補強 (起草時 loogle/Read)**: `EReal.coe_mul_bot_of_pos : 0 < x → (x:EReal) * ⊥ = ⊥`
  (`Operations.lean:579`)、`EReal.mul_bot_of_pos : 0 < x → x * ⊥ = ⊥` (`:591`)、
  `EReal.coe_mul : ↑(x*y) = ↑x * ↑y` (`Basic.lean:146`) が存在し `0 < (2:EReal)` ゆえ
  `2 * ⊥ = ⊥` / `2 * ↑h = ↑(2h)` は **両方とも Mathlib 補題で出る見込み**。残る不確実は
  「`(2 : EReal)` が `↑(2:ℝ)` / `0 < 2` として補題に食わせられるか」の 1 点のみ。Phase A 着手時に
  `(2:EReal) * (⊥:EReal)` を `example` で 1 行検算 (LSP 第 1 戻り) し、補題が直接効かなければ
  即 ℝ≥0∞ 直接 case-split へ退避 (撤退口は def 書換 = 第一選択、sorry 不要)。

---

## Phase B — coercion bridge 群 genuine 化 📋

proof-log: yes (本 Phase 完了時に proof-log 着手)。各 sorry を 1 つずつ埋める (skeleton-driven)。

- [ ] `differentialEntropyExt_of_ac (h : μ ≪ volume) : differentialEntropyExt μ = ↑(differentialEntropy μ)`:
      `unfold differentialEntropyExt` (`irreducible_def` ゆえ `differentialEntropyExt_def` simp) + `if_pos h`。
- [ ] `differentialEntropyExt_singular (h : ¬ μ ≪ volume) : differentialEntropyExt μ = ⊥`: 同上 `if_neg h`。
- [ ] `entropyPowerExt_of_ac (h : μ ≪ volume) : entropyPowerExt μ = ENNReal.ofReal (Real.exp (2 * differentialEntropy μ))`:
      `unfold entropyPowerExt` + `differentialEntropyExt_of_ac h` + `EReal.coe_mul`/`coe_ofNat` で
      `2 * ↑h = ↑(2h)` + `EReal.exp_coe` (`exp ↑x = ENNReal.ofReal (Real.exp x)`)。
- [ ] `entropyPowerExt_singular (h : ¬ μ ≪ volume) : entropyPowerExt μ = 0`:
      `differentialEntropyExt_singular h` + `2 * ⊥ = ⊥` (`EReal.mul_bot_of_pos` / `coe_mul_bot_of_pos`、
      `0 < (2:EReal)`) + `EReal.exp_bot` (`exp ⊥ = 0`)。
- [ ] verify: `lake env lean` clean。`#print axioms entropyPowerExt_of_ac` 等で sorryAx 非依存を確認
      (genuine 完成なら `[propext, Classical.choice, Quot.sound]`、Classical は a.c. 判定由来で許容)。

### Phase B 撤退ライン

- **L-Retype-B-α**: bridge proof が `EReal.mul` の coe 経路 (`(2:EReal) * ↑h = ↑(2h)`) で
  `coe_mul` が `(2:EReal)` を `↑(2:ℝ)` と認識せず詰まる → bridge を `sorry` +
  `@residual(plan:epi-entropypower-retype-plan)` で type-check done のまま残し、定義側を
  ℝ≥0∞ 直接 case-split (L-Uncond-0-δ) に pivot して再証明。**仮説束化禁止** (bridge は
  regularity hyp `μ ≪ volume` のみ取る、`*Hypothesis` predicate に核を bundle しない)。

---

## Phase C — 非自明値 sanity gate (L-Uncond-0-γ 自己監査) 📋

proof-log: yes (退化トラップ除去の verbatim 検証は本 sub-plan の core 価値)。

- [ ] `entropyPowerExt_dirac (m : ℝ) : entropyPowerExt (Measure.dirac m) = 0`:
      `mutuallySingular_dirac m volume` ⟹ `¬ (Measure.dirac m ≪ volume)` ⟹ `entropyPowerExt_singular`。
      **退化トラップ除去の verbatim 検証**: 旧 Real `entropyPower (dirac m) = exp 0 = 1` (誤) →
      新 `entropyPowerExt (dirac m) = 0` (正)。`differentialEntropy_dirac = 0`
      (`DifferentialEntropy.lean:155`、起草時 verbatim 確認済) は Real workhorse 側の値で、
      新 EReal 層は a.c. 判定で `⊥` に落とすため exp で `0` になる (workhorse の `0` を見ない)。
- [ ] `entropyPowerExt_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
      entropyPowerExt (gaussianReal m v) = ENNReal.ofReal (2 * Real.pi * Real.exp 1 * v)`:
      `gaussianReal m v ≪ volume` ⟹ `entropyPowerExt_of_ac` + 旧 `entropyPower_gaussianReal`
      (`EntropyPowerInequality.lean:128`、`= 2πe·v`、`@audit:ok`) を `ENNReal.ofReal` でラップ。
      **a.c. 非自明値 ≠ 0 の gate**: a.c. 測度で LHS が `0` に潰れないこと (定義ミスで a.c. 判定が
      常時 false に転ぶ退化定義悪用の検出)。`ENNReal.ofReal_ne_zero` + `2πe·v > 0` で `≠ 0`。
- [ ] verify: `lake env lean` clean + `#print axioms` sorryAx 非依存。

### Phase C 撤退ライン

- **L-Retype-C-α** (gaussian a.c. 判定): `gaussianReal m v ≪ volume` を供給する Mathlib lemma が
  即座に見つからない → `gaussianReal` の density (`gaussianPDFReal`) 経由 `withDensity` 表示から
  a.c. を導く (inventory §D `gaussianReal` は a.c. 既知)。**禁止**: a.c. 判定を回避するために
  sanity gate 自体を vacuous に書く (それでは退化定義悪用の検出にならない)。詰まったら gate を
  `sorry` + `@residual(plan:epi-entropypower-retype-plan)` で残し、退化検出を Phase 5 assembly
  (親 plan) の独立 honesty-auditor に委ねる旨を docstring 明示。

---

## Phase D — 旧 Real entropyPower 退避判断 + 編入 📋

proof-log: yes (締め)。

- [ ] **旧 Real `entropyPower` (`EntropyPowerInequality.lean:102`) の扱いを決定**: 本 sub-plan は
      **旧 def を消さない** (S2 downstream re-port が consumer 11 file を順次移行するまで温存)。
      新 ℝ≥0∞ 版は `entropyPowerExt` という **別名で共存**させ、S2 で旧→新の置換を段階実施する
      (親 plan L-Uncond-1-β: 旧を `entropyPowerReal` に退避するのは S2 の責務、S1 では別名共存で
      blast radius を 0 に保つ)。⚠ **本 sub-plan で旧 `entropyPower` を rename/削除しない** (11 file
      一斉破壊を避ける、CLAUDE.md olean refresh コスト)。
- [ ] `InformationTheory.lean` に `import InformationTheory.Shannon.EntropyPowerExt` を 1 行追加。
- [ ] verify: `lake env lean InformationTheory/Shannon/EntropyPowerExt.lean` final clean。
      新規 `sorry` + `@residual` が残る場合は親 orchestrator が **独立 honesty-auditor 起動**
      (CLAUDE.md 必須、bridge signature が regularity hyp のみで load-bearing でないこと +
      `@residual` classification `plan:epi-entropypower-retype-plan` の正しさを独立検証)。

### Phase D 撤退ライン

- **L-Retype-D-α** (命名衝突): 新 `entropyPowerExt` を将来 `entropyPower` に昇格する際 (S2 完了後)、
  旧 Real 版との名前衝突が namespace で解決できない → 新版を別 namespace
  (`InformationTheory.Shannon.Ext`) に置くか、旧版を `entropyPowerReal` に退避 (L-Uncond-1-β、S2 責務)。
  本 sub-plan では `entropyPowerExt` 別名のまま着地し、昇格は S2 へ defer。

---

## 撤退ライン一覧 (slug 参照用)

| slug | Phase | 内容 | 退避先 |
|---|---|---|---|
| `L-Uncond-0-δ` | A | `EReal.mul` の `2*⊥`/`2*↑x` 挙動が非分岐定義で想定外 | ℝ≥0∞ 直接 case-split 定義 (def 書換 = 第一選択) |
| `L-Retype-B-α` | B | bridge の `coe_mul` 経路が詰まる | bridge `sorry`+`@residual`、定義を ℝ≥0∞ case-split へ pivot |
| `L-Retype-C-α` | C | gaussian a.c. 判定 lemma 不在 | `gaussianPDFReal` withDensity 経由、gate `sorry`+`@residual` |
| `L-Retype-D-α` | D | 新旧 entropyPower 命名衝突 | 別 namespace or `entropyPowerReal` 退避 (S2 defer) |

全 Phase 共通禁止 (CLAUDE.md 検証の誠実性): `Prop := True` placeholder / 結論型≡仮説型 `:= h` 循環 /
load-bearing `*Hypothesis` predicate に核 bundle / 退化定義悪用 (a.c. 判定の常時 false 倒し)。
honest 撤退口: bridge (proof body) は `sorry` + `@residual(plan:epi-entropypower-retype-plan)`、
def RHS が詰まったら第一選択 = 定義書換、第二選択 = `@audit:defect` + `@audit:closed-by-successor(epi-unconditional-moonshot-plan)`。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-06-05 起草 (非分岐 EReal.exp 定義を確定、ℝ≥0∞ 直接 case-split は退避先)**: 親 plan §Phase 1
   + inventory (Phase 0-A/0-C) を受け、`entropyPowerExt := EReal.exp (2 * differentialEntropyExt μ)`
   の **非分岐定義**を第一候補に確定。case-split は `differentialEntropyExt : EReal` 側に一元化。
   - **起草時 verbatim 確認 (予測でなく実コード Read / loogle)**: `differentialEntropy_dirac = 0`
     (`DifferentialEntropy.lean:155`)、旧 `entropyPower := Real.exp (2*differentialEntropy)`
     (`EntropyPowerInequality.lean:102`)、`entropyPower_pos` (`:109`)、`entropyPower_gaussianReal = 2πe·v`
     (`:128`、`@audit:ok`)。Mathlib `EReal.exp` (`ERealExp.lean:40`)、`exp_bot = 0` (`:42`)、
     `exp_coe = ENNReal.ofReal (Real.exp x)` (`:45`、`rfl`)、`exp_monotone` [gcongr] (`:72`)、
     `exp_top = ∞` (`:44`)、`exp_le_exp_iff` (`:84`)。`klDiv` precedent
     (`KullbackLeibler/Basic.lean:55-58`、`open Classical in` + `irreducible_def` + `if μ ≪ ν ∧ ... then`)。
   - **L-Uncond-0-δ への補強確認 (起草時)**: `EReal.coe_mul_bot_of_pos : 0<x → (x:EReal)*⊥ = ⊥`
     (`Operations.lean:579`)、`EReal.mul_bot_of_pos : 0<x → x*⊥ = ⊥` (`:591`)、
     `EReal.coe_mul : ↑(x*y) = ↑x*↑y` (`Basic.lean:146`) が存在。`0 < (2:EReal)` ゆえ `2*⊥ = ⊥` /
     `2*↑h = ↑(2h)` は Mathlib 補題で出る見込み。残不確実 = `(2:EReal)` を `0<2` / `↑(2:ℝ)` として
     補題に食わせられるか 1 点 (Phase A で `example` 1 行検算 → 詰まれば即 ℝ≥0∞ case-split 退避)。
   - **本 sub-plan は旧 Real `entropyPower` を消さない / rename しない**方針を確定 (Phase D)。新版は
     `entropyPowerExt` 別名で共存、旧→新の consumer 移行 + L-Uncond-1-β 退避は S2 downstream re-port の
     責務に defer。S1 の blast radius を 0 (新 file 1 本 + import 1 行) に保つ。

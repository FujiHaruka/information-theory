# Gambling: side information (Cover–Thomas Theorem 6.1.3) サブ計画

> **Parent**: [`gambling-moonshot-plan.md`](gambling-moonshot-plan.md) §残課題 (side-information 増分)

## 進捗

- [ ] M0 在庫 (再利用 3 補題 verbatim 署名 + 対称 MI 定義形 + reuse-vs-local 判断) 📋
- [ ] Phase 1 — skeleton (def 4 本 + 2 headline + 補助補題を `sorry` 化、root 登録) 📋
- [ ] Phase 2 — marginal / joint が pmf (stdSimplex membership) 📋
- [ ] Phase 3 — オッズ相殺補題 (`sum_comm`) 📋
- [ ] Phase 4 — 条件付き Kelly 最適性 headline #1 📋
- [ ] Phase 5 — 条件付き閉形式組立 `W*(X|Y) = ∑ pX·log o − H(X|Y)` 📋
- [ ] Phase 6 — chain rule bridge `H(X,Y) = H(Y) + H(X|Y)` (正直性の要) 📋
- [ ] Phase 7 — headline #2 `ΔW = I(X;Y)` 組立 📋
- [ ] Phase 8 — 配線 (root / README / roadmap / facts) + 独立 honesty 監査 → `@audit:ok` 📋
- [ ] Phase 9 (optional) — reuse 同値補題 / `ΔW ≥ 0` 系（proof-done 必須外） 📋

## Context

親計画 `gambling-moonshot-plan.md` は Cover–Thomas Ch.6 **Thm 6.1.2**（比例賭け倍加率最適性）を
`InformationTheory/Shannon/Gambling/Basic.lean` で proof-done (sorryAx-free, `@audit:ok`) 済み。
本サブ計画はその隣接定理 **Thm 6.1.3 (gambling with side information)** を拾う: 副情報 Y を得たとき
の倍加率増分 ΔW が相互情報量 I(X;Y) に等しい、という単発恒等式。roadmap の Ch.6 は全体 scope-out
だが、その **解析核 (副情報の倍加率増分 = MI)** のみを genuine closure する（operational な horse-race /
株式市場は scope-out 継続）。

親 Basic.lean は既に恒等式核（オッズ相殺・KL 還元・`doublingRate_proportional_eq` 閉形式）を
提供済みで、本定理はそれらの **周辺化 (marginalization) + 条件付けへの持ち上げ** だけで閉じる。
壁は想定されない。既存共有補題の署名変更は一切しない（consume のみ）ため ripple 無し
（`dep_consumers.sh` 上、Basic.lean の 2 headline の consumer は現状 0 件、本 file が最初の consumer）。

## ゴール / Approach

**ゴール** — 新規 file `InformationTheory/Shannon/Gambling/SideInformation.lean`、namespace
`InformationTheory.Shannon.Gambling`、`variable {α : Type*} [Fintype α] {γ : Type*} [Fintype γ]`。
α = 馬 alphabet (X)、γ = 副情報 alphabet (Y)。表現は **factored form** `(pY, pXgivenY)`:

```lean
-- X-marginal:  pX x = ∑_y pY y · pXgivenY y x
noncomputable def sideMarginalX (pY : γ → ℝ) (pXgivenY : γ → α → ℝ) : α → ℝ :=
  fun x ↦ ∑ y, pY y * pXgivenY y x

-- joint pmf on α × γ:  q(x,y) = pY y · pXgivenY y x
noncomputable def sideInfoJoint (pY : γ → ℝ) (pXgivenY : γ → α → ℝ) : α × γ → ℝ :=
  fun p ↦ pY p.2 * pXgivenY p.2 p.1

-- conditional (side-information) doubling rate of strategy b:
--   W(b | Y) = ∑_y pY y · doublingRate (b y) o (pXgivenY y)
noncomputable def condDoublingRate
    (b : γ → α → ℝ) (o : α → ℝ) (pY : γ → ℝ) (pXgivenY : γ → α → ℝ) : ℝ :=
  ∑ y, pY y * doublingRate (b y) o (pXgivenY y)

-- symmetric pmf mutual information  I(X;Y) = H(X) + H(Y) − H(X,Y)
noncomputable def sideInfoMutualInfo (pY : γ → ℝ) (pXgivenY : γ → α → ℝ) : ℝ :=
  (∑ x, Real.negMulLog (sideMarginalX pY pXgivenY x))       -- H(X)
    + (∑ y, Real.negMulLog (pY y))                          -- H(Y)
    - (∑ p, Real.negMulLog (sideInfoJoint pY pXgivenY p))   -- H(X,Y)
```

**headline 2 本**:

```lean
-- #1 条件付き Kelly 最適性 (副情報 y ごとに比例賭けが条件付き倍加率を最大化)
theorem condDoublingRate_le_proportional
    (b : γ → α → ℝ) (o : α → ℝ) (pY : γ → ℝ) (pXgivenY : γ → α → ℝ)
    (hpY : pY ∈ stdSimplex ℝ γ)
    (hcond : ∀ y, pXgivenY y ∈ stdSimplex ℝ α)
    (hb : ∀ y, b y ∈ stdSimplex ℝ α) (hb_pos : ∀ y x, 0 < b y x)
    (ho : ∀ x, 0 < o x) :
    condDoublingRate b o pY pXgivenY ≤ condDoublingRate pXgivenY o pY pXgivenY

-- #2 headline (CT 6.1.3): ΔW = I(X;Y)
theorem sideInfo_doublingRate_increment_eq_mutualInfo
    (o : α → ℝ) (pY : γ → ℝ) (pXgivenY : γ → α → ℝ)
    (hpY : pY ∈ stdSimplex ℝ γ)
    (hcond : ∀ y, pXgivenY y ∈ stdSimplex ℝ α)
    (ho : ∀ x, 0 < o x) :
    condDoublingRate pXgivenY o pY pXgivenY
      - doublingRate (sideMarginalX pY pXgivenY) o (sideMarginalX pY pXgivenY)
      = sideInfoMutualInfo pY pXgivenY
```

**戦略の全体形（証明の shape）** — オッズ項の周辺化相殺 + 条件付け閉形式 + chain rule bridge:

```
W*(X|Y) := condDoublingRate pXgivenY o pY pXgivenY
         = ∑_y pY y · [ (∑_x pXgivenY y x · log o x) − H(pXgivenY y) ]   (per-y 閉形式)
         = (∑_x pX x · log o x) − H(X|Y)                                (オッズ相殺 Phase 3)
W*(X)    := doublingRate pX o pX = (∑_x pX x · log o x) − H(X)           (pX 閉形式)
ΔW = W*(X|Y) − W*(X) = H(X) − H(X|Y)                                     (log-odds 項が完全相殺)
   = H(X) + H(Y) − H(X,Y)                                               (chain rule Phase 6)
   = sideInfoMutualInfo pY pXgivenY                                     (= I(X;Y))
```

- `H(X|Y) := ∑_y pY y · (∑_x negMulLog (pXgivenY y x))`（条件付きエントロピー、pmf 形）。
- chain rule bridge `H(X,Y) = H(Y) + H(X|Y)` が「対称 MI を recognizable にする」核。

### I(X;Y) の定義形の決定 — 対称形 (H(X)+H(Y)−H(X,Y)) を採用

**決定**: `sideInfoMutualInfo` を **対称形** `H(X) + H(Y) − H(X,Y)` で定義し、chain rule
`H(X,Y) = H(Y) + H(X|Y)` を **genuine 補題** (Phase 6) として建てる。

**根拠 (正直性)**: 非対称形 `I := H(X) − H(X|Y)` で定義すると、headline #2 の結論 `ΔW = I` が
Phase 5 の `ΔW = H(X) − H(X|Y)` と **文字通り同一式** になり trivial/circular に見える（定義を結論に
合わせて作った疑い）。対称形は joint entropy `H(X,Y)` を独立の量として持ち込むため、`ΔW = I` を出すに
は chain rule bridge を **genuine に経由せざるを得ず**、headline が「recognizable mutual information」
になる。honesty 監査の check 4 (sufficiency) を素通りできる非自明恒等式になる。

**トレードオフ**: 対称形は chain rule bridge (Phase 6、per-term `negMulLog(a·b)` 分解 + 各条件付き
pmf の行和 = 1、~30–40 行) を追加で要する。この bridge は Mathlib / in-project に既製が無い
（`rg` 上 pmf-level factored chain rule 不在、既存 `jointEntropy_n` 系は全て measure-theoretic Ω-framework
で本 pmf-framework に噛み合わない）。しかし bundling でも circular でもなく、単発の初等代数で閉じる
軽量補題であり、対称形が与える honesty 上の利得（trivial-circular 回避）に見合う。非対称形の軽さより
対称形の正直性を優先する。

**reuse-vs-local 判断（M0 で確定）**: 対称 pmf MI は既に project 内に
`InformationTheory.Shannon.mutualInfoPmf` (RateDistortion/Achievability.lean、`H(fst)+H(snd)−H(joint)`)
として存在する。これを reuse すれば「project 確立済 MI を参照」で最も recognizable だが、
(a) `RateDistortion.Converse` 経由の重い import chain を Gambling に持ち込む、(b) gambling → rate-distortion
という意味的に逆向きの依存を生む、(c) `mutualInfoPmf` が section variable の `[MeasurableSpace α]` を
署名に引き摺る可能性（M0 で `#check @InformationTheory.Shannon.mutualInfoPmf` により確認）。よって
**primary = local mirror** (`sideInfoMutualInfo` を上記対称形で自前定義)。local mirror は確立済定義と
構造同型ゆえ honesty は同等（対称形 = 標準 MI 公式、crafted ではない）。M0 で import weight が軽微と
判れば Phase 9 で同値補題 `sideInfoMutualInfo = mutualInfoPmf (sideInfoJoint …)` を optional に追加して
anti-duplication を担保する（proof-done 必須外）。

### 正直性メモ（precondition の性質）

全 precondition は **regularity precondition**、load-bearing hypothesis bundling ではない:

- `pY ∈ stdSimplex ℝ γ` — 副情報 Y の真の pmf（定義域制約）
- `∀ y, pXgivenY y ∈ stdSimplex ℝ α` — 各 y で条件付き X-law が pmf（行和 = 1 は chain rule で load-bearing だが
  「命題の核を仮説に encode」ではなく pmf-ness の regularity 制約）
- `∀ x, 0 < o x` — 正のオッズ（親と同じく `log 0 = 0` 規約由来の必須前提）
- headline #1 のみ追加で `∀ y, b y ∈ stdSimplex` + `∀ y x, 0 < b y x`（full-support の賭け戦略、親 #3 と同性質の
  correctness precondition。真の条件付き law `pXgivenY y` 側には positivity 不要 — 最適化対象であり
  `doublingRate_proportional_eq` は p x = 0 を内部処理する）

chain rule / 閉形式は **恒等式 (=)** であり、詰まっても仮説で核を抱えさせる誘惑が構造的に無い。
詰まった箇所は当該補題を `sorry` + `@residual(plan:gambling-side-information-plan)` で撤退する。

## M0 在庫 (verbatim 署名 — 実装前に Phase 0 で再 Read 確認)

再利用は全て既存 sorryAx-free asset。`stdSimplex ℝ α` は Mathlib（`.1 : ∀ a, 0 ≤ P a`、`.2 : ∑ a, P a = 1`）。

**親 Basic.lean（namespace `InformationTheory.Shannon.Gambling`、`variable {α} [Fintype α]`）**:

1. `InformationTheory/Shannon/Gambling/Basic.lean:72`
   `noncomputable def doublingRate (b o p : α → ℝ) : ℝ := ∑ x, p x * Real.log (b x * o x)`
   — 引数順 **(賭け, オッズ, 真の law)**。`doublingRate b o p = ∑ p x · log(b x · o x)`。
2. `Basic.lean:77`
   `theorem doublingRate_proportional_eq (p o : α → ℝ) (hp : p ∈ stdSimplex ℝ α) (ho : ∀ x, 0 < o x) : doublingRate p o p = (∑ x, p x * Real.log (o x)) - ∑ x, Real.negMulLog (p x)`
   — ⚠ **p 自身の positivity は不要**（p x = 0 は内部で場合分け処理）。o > 0 のみ。per-y に `p := pXgivenY y`、
   pX に `p := sideMarginalX pY pXgivenY` で適用。
3. `Basic.lean:124` (`@[entry_point]`, `@audit:ok`)
   `theorem doublingRate_le_proportional (p b o : α → ℝ) (hp : p ∈ stdSimplex ℝ α) (hb : b ∈ stdSimplex ℝ α) (hb_pos : ∀ x, 0 < b x) (ho : ∀ x, 0 < o x) : doublingRate b o p ≤ doublingRate p o p`
   — headline #1 の per-y 材料。`p := pXgivenY y`、`b := b y`。

**Mathlib 側（transitive 供給、`import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`）**:

- `Real.negMulLog (x : ℝ) : ℝ = -x * Real.log x`、`Real.negMulLog 0 = 0`（`Real.negMulLog_zero`）。
- `Real.log_mul (hx : x ≠ 0) (hy : y ≠ 0) : Real.log (x*y) = Real.log x + Real.log y`（両因子 `≠ 0` 必須）。
- `Finset.sum_comm` / `Finset.sum_product` / `Fintype.sum_prod_type`（joint sum の順序入替 + オッズ相殺）。
- `Finset.sum_sub_distrib` / `Finset.mul_sum` / `Finset.sum_congr`（per-term 分解の持ち上げ）。

**reuse 候補（Phase 9 optional のみ、primary では import しない）**:

- `InformationTheory/Shannon/RateDistortion/Achievability.lean` (namespace `InformationTheory.Shannon`,
  `variable {α β} [MeasurableSpace α] [MeasurableSpace β] [Fintype α] [Fintype β]`):
  - `noncomputable def marginalFst (q : α × β → ℝ) : α → ℝ := fun a ↦ ∑ b, q (a, b)`
  - `noncomputable def marginalSnd (q : α × β → ℝ) : β → ℝ := fun b ↦ ∑ a, q (a, b)`
  - `noncomputable def mutualInfoPmf (q : α × β → ℝ) : ℝ := (∑ a, Real.negMulLog (marginalFst q a)) + (∑ b, Real.negMulLog (marginalSnd q b)) - (∑ p, Real.negMulLog (q p))`
  - ⚠ M0 で `#check @InformationTheory.Shannon.mutualInfoPmf` して署名が `[MeasurableSpace _]` を
    引き摺るか確認（引き摺るなら reuse は避け local mirror 一択）。import は `RateDistortion.Converse`
    chain を transitively 引く（重）。

**落とし穴 (pitfall)**:

- 親 `Basic.lean:96` の `doublingRate_gap_eq_klDivPmf` は log-diff 補題経由で `Nonempty α` +
  `MeasurableSpace α`/`MeasurableSingletonClass α` を leak するが、それは Basic.lean 内部 lemma。
  本 file は **`klDivPmf` を直接呼ばず** `doublingRate_le_proportional` / `doublingRate_proportional_eq`
  （instance leak を内部で discharge 済）のみ consume するので、この leak を継承しない見込み。
  chain rule / marginal / オッズ相殺は純 `negMulLog` 代数で `klDivPmf` を経由しない。
- `Real.log_mul` は両因子 `≠ 0` が要る。chain rule per-term は `pY y = 0` / `pXgivenY y x = 0` を
  先に場合分け（両辺 0 で一致）してから `0 < ·` の枝で `log_mul` を firing すること（親 #2 の
  `rcases eq_or_lt_of_le (hp.1 x)` パターンを踏襲）。
- `sideInfoJoint` の sum は `α × γ` 上。chain rule では `∑ p : α×γ = ∑ y, ∑ x`（`Fintype.sum_prod_type`
  + `Finset.sum_comm`）で **y を外側** に取ってから固定 y で per-term 分解する。

## Phase 詳細

### M0 — 在庫確認（proof-log: no）
- [ ] 上記 3 補題（親 Basic.lean）+ NegMulLog API の verbatim 署名を再 Read 確認。
- [ ] `#check @InformationTheory.Shannon.mutualInfoPmf` で MeasurableSpace 引き摺りの有無を確認 →
      reuse-vs-local を確定（primary = local mirror、Phase 9 の同値補題を採るか判断）。
- [ ] `doublingRate_proportional_eq` が p の positivity 不要であること（p x = 0 内部処理）を verbatim 再確認。

### Phase 1 — skeleton（proof-log: no）
- [ ] 新 file `InformationTheory/Shannon/Gambling/SideInformation.lean`、imports = `Meta.EntryPoint` +
      `Shannon.Gambling.Basic` + `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`、namespace + `variable`。
- [ ] def 4 本（`sideMarginalX` / `sideInfoJoint` / `condDoublingRate` / `sideInfoMutualInfo`）を書く。
- [ ] 補助補題 5 本 + headline 2 本を `:= by sorry` で state（下記名で予約）。
- [ ] `InformationTheory.lean` に `import InformationTheory.Shannon.Gambling.SideInformation` を追記
      （既存 `Gambling.Basic` 行 (`InformationTheory.lean:276`) の直後）。
- [ ] Write 後 LSP `<new-diagnostics>` で skeleton が型検査を通す（sorry 警告のみ）ことを確認。

### Phase 2 — marginal / joint が pmf（proof-log: no）
- [ ] `sideMarginalX_mem_stdSimplex (hpY) (hcond) : sideMarginalX pY pXgivenY ∈ stdSimplex ℝ α`
      — 非負は `Finset.sum_nonneg`、和 = 1 は `∑_x ∑_y = ∑_y pY·(∑_x pXgivenY y) = ∑_y pY·1 = 1`
      （`Finset.sum_comm` + 各 `(hcond y).2`）。
- [ ] `sideInfoJoint_mem_stdSimplex (hpY) (hcond) : sideInfoJoint pY pXgivenY ∈ stdSimplex ℝ (α × γ)`
      — 非負は積の非負、和 = 1 は `∑_(x,y) pY y·pXgivenY y x = ∑_y pY y·(∑_x pXgivenY y x) = 1`。
- [ ] （必要なら）marginal 同定 `∀ x, ∑_y sideInfoJoint (x,y) = sideMarginalX … x` / `∀ y, ∑_x sideInfoJoint (x,y) = pY y`。
      local mirror なら `sideInfoMutualInfo` の第1項が既に `sideMarginalX`・第2項が `pY` なのでこの同定は
      Phase 7 で直接は不要（reuse 版 Phase 9 でのみ要る）。

### Phase 3 — オッズ相殺補題（proof-log: no）
- [ ] `sideInfo_logOdds_cancel : ∑ y, pY y * (∑ x, pXgivenY y x * Real.log (o x)) = ∑ x, (sideMarginalX pY pXgivenY x) * Real.log (o x)`
      — `Finset.sum_comm` で `∑_y ∑_x → ∑_x ∑_y`、`Finset.sum_mul` / `mul_comm`・結合で
      `∑_x (∑_y pY y·pXgivenY y x)·log o x`。仮説不要（純代数、o の符号も無関係）。

### Phase 4 — 条件付き Kelly 最適性 headline #1（proof-log: no）
- [ ] `condDoublingRate_le_proportional` — per-y に `doublingRate_le_proportional (pXgivenY y) (b y) o (hcond y) (hb y) (hb_pos y) ho`
      で `doublingRate (b y) o (pXgivenY y) ≤ doublingRate (pXgivenY y) o (pXgivenY y)`、`pY y ≥ 0`
      (`(hpY.1 y)`) で重み付けし `Finset.sum_le_sum`。恒等式でなく不等式だが bundling 無し。

### Phase 5 — 条件付き閉形式組立（proof-log: yes — 中心計算）
- [ ] `condDoublingRate_proportional_eq (hpY) (hcond) (ho) : condDoublingRate pXgivenY o pY pXgivenY = (∑ x, (sideMarginalX pY pXgivenY x) * Real.log (o x)) - ∑ y, pY y * (∑ x, Real.negMulLog (pXgivenY y x))`
      — 各 y で `doublingRate_proportional_eq (pXgivenY y) o (hcond y) ho`、`pY y ·[A_y − B_y]` を
      `Finset.mul_sum` / `Finset.sum_sub_distrib` で分配し、第1項に Phase 3 のオッズ相殺を適用。
      RHS 第2項 = `H(X|Y)`。
- [ ] proof-log に「per-y 閉形式 → 分配 → オッズ相殺」の流れと `p x = 0` 場合分けの所在を記録。

### Phase 6 — chain rule bridge（proof-log: yes — 正直性の要）
- [ ] `sideInfoJointEntropy_eq_chain (hpY) (hcond) : (∑ p, Real.negMulLog (sideInfoJoint pY pXgivenY p)) = (∑ y, Real.negMulLog (pY y)) + ∑ y, pY y * (∑ x, Real.negMulLog (pXgivenY y x))`
      — `∑_p : α×γ = ∑_y ∑_x`（`Fintype.sum_prod_type` + `Finset.sum_comm` で y 外側）。固定 y で
      per-term: `negMulLog (pY y · pXgivenY y x)` を (i) `pY y = 0` → 両辺 0、(ii) `pXgivenY y x = 0` →
      `negMulLog 0 = 0` + RHS 側 `pY y·0`、(iii) 両 > 0 → `Real.log_mul` で分解し
      `∑_x [-pY y·pXgivenY y x·(log pY y + log pXgivenY y x)]`。`∑_x pXgivenY y x = 1` ((hcond y).2) で
      `-pY y·log pY y·1 = negMulLog (pY y)` を切り出し、残りが `pY y·∑_x negMulLog (pXgivenY y x)`。
- [ ] proof-log に per-term 3 場合分け + 行和 = 1 の使い所を記録（bundling でなく恒等式であることを明記）。

### Phase 7 — headline #2 組立（proof-log: no）
- [ ] `sideInfo_doublingRate_increment_eq_mutualInfo` — LHS を Phase 5 (`condDoublingRate_proportional_eq`) +
      `doublingRate_proportional_eq (sideMarginalX …) o (Phase 2 の membership) ho` で
      `(∑ pX·log o − H(X|Y)) − (∑ pX·log o − H(X)) = H(X) − H(X|Y)` に簡約。
      RHS (`sideInfoMutualInfo`) を Phase 6 chain rule で `H(X) + H(Y) − (H(Y) + H(X|Y)) = H(X) − H(X|Y)`
      に簡約。両辺一致で `linarith` / `ring`。
- [ ] `H(X) = ∑_x negMulLog (sideMarginalX … x)` が `sideInfoMutualInfo` 第1項と定義一致していることを確認。

### Phase 8 — 配線 + 独立 honesty 監査（proof-log: no）
- [ ] root import は Phase 1 で登録済 → `lake build InformationTheory.Shannon.Gambling.SideInformation`
      で clean 確認、headline 2 本を `#print axioms` で sorryAx-free (`[propext, Classical.choice, Quot.sound]`) 確認。
- [ ] README 定理表: `docs/readme-theorems.txt` の Ch.6 節に headline 2 本を追記 →
      `gen_readme_table.ts --write`（表本体は手編集不可、実装セッションが実施）。
- [ ] roadmap Ch.6 行に「6.1.3 副情報増分 = MI」注記追記（scope-out 継続注記は残す）。
- [ ] `docs/shannon/shannon-facts.md` に再検証コマンド追記。
- [ ] **独立 honesty 監査必須**: 新 `def sideInfoMutualInfo`（対称 MI）+ chain rule bridge を
      `honesty-auditor` に付す（対称形が trivial-circular でないこと・precondition が regularity のみで
      load-bearing でないこと・check 4 sufficiency を確認）→ headline 2 本を `@audit:ok`。

### Phase 9 (optional — proof-done 必須外、proof-log: no)
- [ ] (a) reuse 同値補題 `sideInfoMutualInfo pY pXgivenY = InformationTheory.Shannon.mutualInfoPmf (sideInfoJoint pY pXgivenY)`
      （M0 で import weight 軽微と判った場合のみ、marginal 同定 Phase 2 経由で anti-duplication 担保）。
- [ ] (b) 「副情報は損しない」corollary `0 ≤ ΔW`（= `sideInfoMutualInfo ≥ 0`）。
      pmf 対称 MI の非負は `klDivPmf (sideInfoJoint) (product-of-marginals) ≥ 0` 経由が要り、既製ブリッジが
      無ければ本 corollary は見送る（2 headline の proof-done には不要）。詰まれば
      `sorry` + `@residual(plan:gambling-side-information-plan)` で撤退し optional のまま残す。

## 規模見積 / 想定壁

- **規模**: 新 file 1 本、def 4 + 補助補題 5 + headline 2 ≈ 250–350 行。全て初等 `negMulLog`/`log` 代数 +
  `Finset` sum 補題 + 親 Basic.lean の 2 headline 再利用。最重は Phase 6 chain rule (~40 行)。
- **想定壁**: **無し**（公算大）。全補題は既存 sorryAx-free asset の再利用 + 周辺化・条件付け・chain rule の
  初等代数。Mathlib gap は生じない見込み。ただし壁判定を loogle 0-hit だけで確定しない（CLAUDE.md
  「壁を宣言するとき」）: chain rule / オッズ相殺は self-build 前提で計画済（既製不在は確認済だが、
  「命題が Mathlib に無い」ではなく「pmf-framework の初等組立」= plumbing であり壁ではない）。
- **署名変更 ripple**: 無し。既存共有補題は consume のみ、本 file が Basic.lean 2 headline の最初の consumer。

## 撤退ライン（retreat）

各解析 Phase で詰まった場合、**当該補題の signature を保ったまま body を `sorry` + `@residual(plan:gambling-side-information-plan)`**
で撤退する（hypothesis bundling / `*Hypothesis` predicate 化は禁止）。想定壁は無いので `wall:` は使わない。
特に:

- Phase 5 `condDoublingRate_proportional_eq` / Phase 6 `sideInfoJointEntropy_eq_chain` は恒等式。詰まっても
  仮説で核を抱えさせず、恒等式の形のまま `sorry` を残す。
- Phase 9 (a)(b) は proof-done 必須外。詰まれば optional のまま `sorry` + 上記 residual で残置してよい
  （2 headline の proof-done 判定には影響しない）。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除（git が履歴）、active な判断のみ残す。

1. **I(X;Y) 定義形 = 対称形 (H(X)+H(Y)−H(X,Y))**: 非対称形は結論と同一式で trivial-circular に
   見えるため対称形採用、chain rule bridge (Phase 6) を genuine に建てて recognizable MI 化。トレードオフ
   （bridge 追加 ~40 行 vs 正直性）は正直性を優先。詳細は Approach「I(X;Y) の定義形の決定」。
2. **reuse-vs-local mirror**: primary = local mirror（`RateDistortion` 経由の重 import + gambling→RD 逆依存 +
   `mutualInfoPmf` の MeasurableSpace 引き摺り懸念を回避）。M0 で import weight を確認し軽微なら
   Phase 9(a) 同値補題で anti-duplication を担保。

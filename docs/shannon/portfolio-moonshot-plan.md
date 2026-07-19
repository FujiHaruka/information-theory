# Portfolio (log-optimal) ムーンショット計画 🌙

> **Parent**: [`gambling-moonshot-plan.md`](gambling-moonshot-plan.md) — Ch.6 `doublingRate` の非対角一般化

Cover–Thomas *Elements of Information Theory* 2nd ed **Ch.16 "Information Theory and Investment"** の
log-optimal portfolio を、有限アウトカム版で **proof-done** (0 sorry / 0 @residual / sorryAx-free /
独立 `@audit:ok`) まで形式化する。Ch.16 は当初 `docs/textbook-roadmap.md` で章単位 `✖ scope-out` だったが、
本計画がその tractable な解析核 (concavity / Kuhn–Tucker / competitive optimality の 3 中核定理) を
genuine closure し、roadmap Ch.16 は `✅` へ復帰済 (operational な株式市場・連続時間投資は scope-out 継続)。

全 Mathlib API は在庫で verbatim 署名 + 型クラス前提込みで確定済み・**Mathlib 壁ゼロ**
([`portfolio-mathlib-inventory.md`](portfolio-mathlib-inventory.md) が SoT)。本 plan は在庫テーブルを
重複させず節参照 (`→ 在庫 §A` 等) で済ませ、戦略・Phase 分割・statement・撤退ライン・DoD に集中する。

コードは新規 file `InformationTheory/Shannon/Portfolio/Basic.lean`、namespace
`InformationTheory.Shannon.Portfolio`。

## 進捗 — ✅ DONE (2026-07-19)

- [x] Phase 0 — M0 在庫再確認 → [`portfolio-mathlib-inventory.md`](portfolio-mathlib-inventory.md)
- [x] P1 — `competitive_optimality` (gateway atom、CT 16.6.1) — proof-done sorryAx-free + @audit:ok
- [x] P2 — `growthRate_concaveOn` (CT 16.2.2) — proof-done sorryAx-free + @audit:ok
- [x] P3 — `logOptimal_of_kuhnTucker` (reverse KT、CT 16.2.1) — proof-done sorryAx-free + @audit:ok
- [x] P4 — `kuhnTucker_of_logOptimal` (forward KT、CT 16.2.1) — proof-done sorryAx-free + @audit:ok（**撤退ライン不発**、FDeriv-at-max を無条件で構築）
- [x] P5 — 配線 (root import 登録 / README 表 / roadmap Ch.16 `✅` / 独立監査 honesty+style 両 PASS)

**Closure summary**: 4 headline 定理すべて proof-done (0 sorry / 0 @residual / sorryAx-free
`[propext, Classical.choice, Quot.sound]` / 独立 `honesty-auditor` PASS で `@audit:ok`)。`competitive_optimality`
の gateway probe が def 形の Mathlib 適合を確認し、以降 concavity → reverse KT → forward KT が予定どおり壁なく着地。
support 上等号 (`bs_i > 0 ⟹ KT_i = 1`) は headline に含めず未実装 (CT 16.2.1 の `≤ 1` 方向で closure)。
実装差分 2 点 → 判断ログ 3/4。

## Sub-plan 一覧

静的核 (本計画、CT 16.2 concavity / 16.2.1 KT / 16.6.1 competitive) の operational / universal 拡張は
子計画に分離。子が状態の SoT (衝突時は親を子に合わせる)。

| Sub-plan | scope | 状態 |
|---|---|---|
| [`portfolio-operational-plan.md`](portfolio-operational-plan.md) | CT §16.3 (AO-iid) / §16.4 (side-info) / §16.5 (stationary) / §16.7 (universal) の operational / universal 定理 | Leg A/B-core/C/D **proof-done + @audit:ok**、Leg B 完全形 (W_∞ AEP、CT 16.5.1) は後継 [`portfolio-stationary-woo-plan.md`](portfolio-stationary-woo-plan.md) で進行中 (R1 + R2 proof-done + @audit:ok、R3/R4 残) |

**CT 節ラベル (2nd ed 実節に是正済)**: §16.2 KT characterization / §16.3 asymptotic optimality (iid、子 Leg A) /
§16.4 side info / §16.5 stationary markets / §16.6 competitive optimality (`competitive_optimality` = **Thm 16.6.1**) /
§16.7 universal portfolios。本計画 P1 を過去 "16.3.1" と誤ラベルしていたのを 16.6.1 に修正 (16.3.1 は子 Leg A)。

## ゴール / Approach

**ゴール** — 有限型 `α` `[Fintype α]` (アウトカム)、`m : ℕ` (株数)、真の pmf `p ∈ stdSimplex ℝ α`、
price-relative `X : α → (Fin m → ℝ)` (各 `X a i ≥ 0`)、portfolio `b ∈ stdSimplex ℝ (Fin m)`。以下 3 中核
(4 定理) を headline とする:

- **CT 16.2.2** `growthRate_concaveOn` — 成長率 W は portfolio simplex 上で凹。
- **CT 16.2.1** `logOptimal_of_kuhnTucker` / `kuhnTucker_of_logOptimal` — log-optimal ⟺ Kuhn–Tucker 条件
  `∀ i, ∑ a, p a · X a i / S_{b*}(a) ≤ 1` (support 上等号)。
- **CT 16.6.1** `competitive_optimality` — KT portfolio `b*` に対し任意 `b` で `E[S_b / S_{b*}] ≤ 1`。

**Approach — gambling からの分岐点が本 plan の核**。gambling (Ch.6, DONE) は対角 price-relative
(`X a i = o i · [a = i]`) の特殊形で、gap が per-term に log 分離するため **KL 還元** (`klDivPmf p b` の
Gibbs 非負性) で閉じた。portfolio の一般 (非対角) X では `log(∑ i b_i X_{a,i})` が per-term 分離せず
**KL 還元は効かない** (在庫 §G)。したがって証明ルートは **凹性 + 有限 Jensen** に分岐する:

- **凹性 (P2)** = `Real.log` の `Ioi 0` 上の凹性 (`strictConcaveOn_log_Ioi`) を linear form `S_b(a)` に
  `ConcaveOn.comp_linearMap` で前合成 → `p a ≥ 0` で `.smul` → `∑ a` を畳む (在庫 §A)。
- **reverse KT (P3)** = 凹性 + 有限 log-Jensen (`ConcaveOn.le_map_sum`)。`W(b*) − W(b) ≥ −log(∑ i b_i · KT_i)
  ≥ −log 1 = 0`。**calculus 不要** (在庫 §B)。
- **competitive (P1)** = KT 仮定下に `Finset.sum_comm` + `mul_sum` の純代数、微分ゼロ (在庫 §F)。
- **forward KT (P4)** = **唯一の calculus**。simplex 上の最大点 `b*` の一階条件を `IsLocalMaxOn.
  hasFDerivWithinAt_nonpos` に方向 `e_i − b*` を渡して取り出す (在庫 §E)。W の `HasFDerivWithinAt` は
  `HasFDerivWithinAt.sum`/`.log` + linear form で構築 = plumbing、壁ではない。

構造上、微分は **forward KT (P4) にのみ現れる**。したがって着手順は「微分ゼロの atom を先に」
= P1 (gateway) → P2 → P3 → P4 (最大重量) が最短・最安。

## 中核 def (Mathlib-shape-driven、確定形)

在庫 §着手skeleton の形をそのまま採用する。`log(linear form)` は `ConcaveOn.comp_linearMap` と
`ConcaveOn.le_map_sum` の結論形に直接乗るため、**textbook 丸写しでよい珍しいケース** (Mathlib-shape 駆動の
再定義が不要)。

```lean
/-- Wealth relative `S_b(a) = ∑ i, b i · X a i`. -/
noncomputable def wealthRelative (X : α → Fin m → ℝ) (b : Fin m → ℝ) (a : α) : ℝ :=
  ∑ i, b i * X a i

/-- Growth (doubling) rate `W(b) = ∑ a, p a · log (S_b(a))`. -/
noncomputable def growthRate (p : α → ℝ) (X : α → Fin m → ℝ) (b : Fin m → ℝ) : ℝ :=
  ∑ a, p a * Real.log (wealthRelative X b a)
```

**file 配置**: `InformationTheory/Shannon/Portfolio/Basic.lean` を推奨 (gambling と同 family の別ディレクトリ)。
在庫工数感 (~300–400 行、gambling ~150 行の 2–3 倍) からは 1 ファイルで >1500 行にはならない見込みだが、
forward KT の FDeriv 構築が肥大した場合は `Portfolio/KuhnTucker.lean` へ分割余地あり (P4 着手時に判断)。

## Phase 0 — M0 在庫再確認 📋

proof-log: no。在庫 §A–G の verbatim 署名 (型クラス前提込み) と Key-preconditions box を実装直前に再 Read し、
`Real.log` の凹性定義域が `Set.Ioi 0` (開) である点・`ConcaveOn.comp_linearMap` の結論定義域が
`g ⁻¹' (Ioi 0)` = `{b | S_b(a) > 0}` である点を確認する。在庫が SoT ゆえテーブル転記はしない。

- [ ] 在庫 §A/§B/§E の署名を再 Read (`ConcaveOn.comp_linearMap` / `ConcaveOn.le_map_sum` /
      `IsLocalMaxOn.hasFDerivWithinAt_nonpos` / `mem_posTangentConeAt_of_segment_subset`)
- [ ] skeleton (imports + namespace + def 2 本 + 定理 4 本 `:= by sorry`) を Write、type-check done を確認
- [ ] root `InformationTheory.lean` に import 行を追加

## P1 — `competitive_optimality` (gateway atom、CT 16.6.1) ✅

proof-log: no。**最初に着手する decisive atom**。def の形が Mathlib 補題に乗るか + KT 意味論が正しいかを
最小コストで検証する。KT を仮定した純代数 (`Finset.sum_comm` + `mul_sum` + `sum_le_sum` + `hb.2`)、
微分・凹性ともに不要、~20 行 (在庫 §F)。

```lean
theorem competitive_optimality (p : α → ℝ) (X : α → Fin m → ℝ) (bs b : Fin m → ℝ)
    (hb : b ∈ stdSimplex ℝ (Fin m)) (hpos : ∀ a, 0 < wealthRelative X bs a) (hXnn : ∀ a i, 0 ≤ X a i)
    (hKT : ∀ i, (∑ a, p a * X a i / wealthRelative X bs a) ≤ 1) :
    (∑ a, p a * (wealthRelative X b a / wealthRelative X bs a)) ≤ 1
```

- [ ] `∑ a p_a S_b/S_{b*} = ∑ i b_i (∑ a p_a X_{a,i}/S_{b*}) = ∑ i b_i · KT_i ≤ ∑ i b_i = 1` を組む
- [ ] gateway 判定: def 形が Mathlib 補題に乗り KT 意味論が正しいことを確認 (乗らなければ def / KT 署名を再設計)

## P2 — `growthRate_concaveOn` (CT 16.2.2) 📋

proof-log: yes (`ConcaveOn.sum` 自作 induction は再利用可能な糊、記録に値する)。在庫 §A のチェーン +
有限和版 `ConcaveOn.sum` の自作 induction (`Finset.cons_induction` + `.add` + `concaveOn_const`、~15 行、
Mathlib 不在の唯一の汎用ギャップ)。計 ~40 行。

```lean
theorem growthRate_concaveOn (p : α → ℝ) (X : α → Fin m → ℝ) (hp : p ∈ stdSimplex ℝ α)
    (hpos : ∀ a, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < wealthRelative X b a) :
    ConcaveOn ℝ (stdSimplex ℝ (Fin m)) (growthRate p X)
```

- [ ] `S_b(a)` を linear form (`∑ i, X a i • LinearMap.proj i`) で構成
- [ ] `strictConcaveOn_log_Ioi.concaveOn |>.comp_linearMap |>.smul (hp.1 a)` で各項の凹性
- [ ] `hpos` で凹性定義域を simplex 全体へ (preconditions box)、`ConcaveOn.sum` 糊で `∑ a` を畳む

## P3 — `logOptimal_of_kuhnTucker` (reverse KT、CT 16.2.1) 📋

proof-log: no。P2 の凹性 + 有限 log-Jensen (`ConcaveOn.le_map_sum`、在庫 §B)。**calculus 不要**、~50 行。

```lean
theorem logOptimal_of_kuhnTucker (p : α → ℝ) (X : α → Fin m → ℝ) (bs : Fin m → ℝ)
    (hp : p ∈ stdSimplex ℝ α) (hbs : bs ∈ stdSimplex ℝ (Fin m))
    (hpos : ∀ a, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < wealthRelative X b a)
    (hKT : ∀ i, (∑ a, p a * X a i / wealthRelative X bs a) ≤ 1) :
    IsMaxOn (growthRate p X) (stdSimplex ℝ (Fin m)) bs
```

- [ ] 任意 `b ∈ simplex` で `W(bs) − W(b) = −∑ p_a log(S_b/S_{bs}) ≥ −log(∑ p_a S_b/S_{bs})` (`le_map_sum`)
- [ ] `∑ p_a S_b/S_{bs} = ∑ i b_i · KT_i ≤ 1` (P1 の代数を再利用) → `−log(≤1) ≥ 0` で `IsMaxOn`

## P4 — `kuhnTucker_of_logOptimal` (forward KT、CT 16.2.1) + support 等号 📋

proof-log: yes (多次元 FDeriv-at-max の構築は本 family 初、記録に値する)。**最大重量**。W の
`HasFDerivWithinAt` 構築 (~60–100 行) + support 上等号 (~15 行)。機構は完備 (壁ゼロ、在庫 §E)、
`.sum`/`.log` 合成の plumbing。

```lean
theorem kuhnTucker_of_logOptimal (p : α → ℝ) (X : α → Fin m → ℝ) (bs : Fin m → ℝ)
    (hp : p ∈ stdSimplex ℝ α) (hbs : bs ∈ stdSimplex ℝ (Fin m))
    (hpos : ∀ a, 0 < wealthRelative X bs a) (hXnn : ∀ a i, 0 ≤ X a i)
    (hmax : IsMaxOn (growthRate p X) (stdSimplex ℝ (Fin m)) bs) :
    ∀ i, (∑ a, p a * X a i / wealthRelative X bs a) ≤ 1
```

- [ ] W の `HasFDerivWithinAt` を `HasFDerivWithinAt.sum` + `.log` + linear form FDeriv で構築
      (`f' = ∑ a, p a · (S_{bs}(a))⁻¹ • dual`、`f'(e_i − bs) = KT_i − 1`)
- [ ] `IsMaxOn.localize` → `IsLocalMaxOn.hasFDerivWithinAt_nonpos` に方向 `e_i − bs` を渡す
      (`single_mem_stdSimplex` + `convex_stdSimplex.segment_subset` で tangent cone 所属) → `KT_i − 1 ≤ 0`
- [ ] support 等号 `bs_i > 0 ⟹ KT_i = 1`: `∑ i bs_i (KT_i − 1) = 0` かつ各項 `≤ 0` から (~15 行)

## 正直性メモ (regularity precondition の性質)

凹性 (P2) / Jensen (P3) / log 微分 (P4) はいずれも **`S_b(a) > 0` (positivity)** を要する
(例えば `∀ a i, 0 < X a i`、あるいは simplex 上一様の `hpos`)。これは gambling `hb_pos` と同性質で、
`Real.log 0 = 0` 規約に由来する **regularity precondition であって load-bearing hypothesis bundling では
ない** (proof-done と両立、honesty gate 通過の前提)。根拠:

- `strictConcaveOn_log_Ioi` は開区間 `Ioi 0` 上でのみ凹。`hpos` を落とすと頂点 `b = e_i` で `S_b(a) = X a i
  = 0` になりうる点で凹性が破れる (境界、在庫 preconditions box)。
- 証明の**核心** (KL の代替として凹性+Jensen で不等式を出す論理) は本文が担い、`hpos` は定義域制約のみを
  pin する。`*Hypothesis` predicate に核を抱えさせる形は取らない。撤退時 (下記) も retreat exit は sorry のみ。

## 撤退ライン

在庫が **Mathlib 壁ゼロ**を確認済 (機構 §A–F 完備) ゆえ発動リスクは低い。ただし多次元 FDeriv-at-max は
本 family 初のため非ゼロ。

- **発動条件**: forward KT (P4) の W の `HasFDerivWithinAt` 構築が想定 (~100 行) を超えて詰まった場合。
- **縮退着地**: P1 (competitive) / P2 (concavity) / P3 (reverse KT) の **3 本で着地**し、forward KT
  (`kuhnTucker_of_logOptimal`) のみ body を `sorry` + `@residual(plan:portfolio-forward-kt)` で残置する
  (**hypothesis 束ねはしない、retreat exit は sorry のみ**)。この縮退でも CT 16.2.2 / 16.2.1-reverse /
  16.6.1 = **3/4 が genuine closure**。forward KT は後続 `portfolio-forward-kt-plan.md` へ分離 (slug 整合)。
- **gateway-atom-first**: P4 の撤退判断より前に、既に P1 (gateway atom) を着地済のため def 形・KT 意味論は
  検証済 = 撤退しても手戻りは P4 の calculus 部のみ。

## DoD / gate

- **各 Phase**: type-check done (`lake env lean` 0 error、`sorry` は `@residual` 付き) で commit/push 可。
  proof-done (0 sorry ∧ 0 @residual、file 内) が genuine 完成。
- **headline `@[entry_point]`**: 4 定理 `competitive_optimality` / `growthRate_concaveOn` /
  `logOptimal_of_kuhnTucker` / `kuhnTucker_of_logOptimal` を `@[entry_point]` に。proof-done + 独立
  `honesty-auditor` PASS で `@audit:ok`。
- **honesty gate**: P1–P4 で新規 `sorry` + `@residual` を導入した commit (撤退時の forward KT) は独立
  `honesty-auditor` 必須 (regularity precondition が load-bearing でない旨も検査対象)。
- **style gate**: `Basic.lean` の decl/docstring 追加 (全 Phase) で `style-auditor` を touched file に適用。

## 完了時の配線

- **root**: `InformationTheory.lean` に `import InformationTheory.Shannon.Portfolio.Basic` を登録 (Phase 0 で先行)。
- **README**: `docs/readme-theorems.txt` に `@ 16 | Portfolio theory (log-optimal)` 節 + 4 headline を追記し、
  `deno run -A scripts/gen_readme_table.ts --write` で表を再生成 (marker 内は手編集しない)。
- **roadmap**: `docs/textbook-roadmap.md` の Ch.16 行 (現 `| 16 | Portfolio | ✖ | — |`) を解析核復帰へ更新
  (gambling Ch.6 の `🟡 (倍加率最適性)` + scope-out 注記のミラー)。
- **facts**: `docs/shannon/shannon-facts.md` に headline の sorryAx-free 再検証コマンドを追記。
- **parent 同期**: 本 plan の状態変化時は parent `gambling-moonshot-plan.md` の子プラン行も同期 (子が SoT)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)。

1. **撤退ライン (resolved 2026-07-19、不発)**: forward KT (P4) の多次元 FDeriv-at-max は想定内 (~実装で closure)
   で着地し、縮退 (3/4) は発動せず。`portfolio-forward-kt` slug は使わず終い。
2. **precondition packaging (resolved)**: concavity/reverse KT は simplex 上一様 `hpos`、forward KT は `bs`
   のみの positivity で確定 (在庫 skeleton の 2 形を踏襲)。honesty gate で全て regularity precondition と判定。
3. **forward KT の hXnn 削除 (resolved 2026-07-19)**: skeleton 署名は `hXnn : ∀ a i, 0 ≤ X a i` を持っていたが、
   forward KT の FDeriv/tangent-cone 論法は X の符号に非依存で hXnn を一切使わず → honest な強化として signature
   から削除 (honesty-auditor が「theorem-hypothesis の削除は monotone-safe、falseness risk なし」と検証、`@audit:ok`)。
   `competitive_optimality` は skeleton どおり hXnn/hpos を保持 (前セッションで proof-done、未変更)。

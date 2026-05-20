# Wyner–Ziv `WynerZivCondEntDiffConvex` full discharge — moonshot plan 🌙

> 実態整合 (2026-05-20): **DONE-UNCOND (L-WZ3 凸性 full discharge 達成) — plan の「実装未着手 / Phase 1-6 全 `[ ]`」表記は STALE、実装完了**。`Common2026/Shannon/WynerZivCondEntDiffConvexBody.lean` (20628 B, 0 sorry, `True` placeholder なし)。主定理 `wynerZivCondEntDiffConvex_holds` (WynerZivCondEntDiffConvexBody.lean:354) は唯一の honest hyp `h_pmf_nn : ∀p, 0 ≤ P_XY p` の下で `WynerZivCondEntDiffConvex` を **無条件 (第一目標) 証明** — per-u block convexity `wzCondEntDiff_block_convex` (:214、`log_sum_inequality_negMulLog` per-atom 路線) を `∑_u` 集約。unconditional rate wrapper `wynerZivRateFactorizable_convex_in_D_unconditional` (:372) で `_of_condEntDiff` の `h_core` を消去 (`h_pmf : P_XY ∈ stdSimplex` から `h_pmf.1` 供給、rate-level 真 unconditional)。affine 翻訳 `wzMarginalXU/YU_smul_add` (:47,:55)、block↔joint 同一視 (:337) も実証明。FLAW なし。Common2026.lean に import 済 (line 226)。
>
> **Status**: 計画起草のみ (2026-05-20)。実装未着手。
>
> **target**: 教科書ロードマップ (`docs/textbook-roadmap.md:710`) が「残存 frontier gap = joint perspective convexity of ...」と名指しした Wyner–Ziv rate function 凸性 (Cover–Thomas Lemma 15.9) の **irreducible analytic core** を **無条件で full discharge** する。周辺 (`H(U)` cancellation, `H(X)−H(Y)` constancy, assembly, rate wrapper) は `WynerZivObjectiveConvexityBody.lean` で全 discharge 済。残るのは 1 つの凸性述語 `WynerZivCondEntDiffConvex` だけ。
>
> **関連**:
> - 在庫: [`wyner-ziv-convexity-discharge-mathlib-inventory.md`](wyner-ziv-convexity-discharge-mathlib-inventory.md) — verdict (b)、自前 150–300 行。
> - 前段 plan: [`wyner-ziv-discharge-moonshot-plan.md`](wyner-ziv-discharge-moonshot-plan.md) (D-antitone + plumbing)。
> - frame: `Common2026/Shannon/WynerZivObjectiveConvexityBody.lean`。

## 進捗

- [ ] Phase 0 — 在庫 verdict 確認 + 前提リスク確定 (`P_XY ≥ 0` / `h_ac`) ✅ (在庫済、本 plan は再確認のみ) → [inventory](wyner-ziv-convexity-discharge-mathlib-inventory.md)
- [ ] Phase 1 — skeleton 配置 (helper を `:= by sorry` で並べて型検査) 📋
- [ ] Phase 2 — affine 翻訳補題群 (marginal の凸結合化) 📋
- [ ] Phase 3 — `h_ac` 充足補題 (絶対連続性を marginal 構造から落とす) 📋
- [ ] Phase 4 — per-`u` block 凸性補題 (`log_sum_inequality_negMulLog` を当てる) 📋
- [ ] Phase 5 — `∑_u` 集約 + 2-point Jensen 縮約 → 主定理 `wynerZivCondEntDiffConvex_holds` 📋
- [ ] Phase 6 — unconditional rate wrapper re-publish (`_of_condEntDiff` の `h_core` を消す) 📋

## ゴール / Approach

新ファイル `Common2026/Shannon/WynerZivCondEntDiffConvexBody.lean` で、`WynerZivObjectiveConvexityBody.lean:212` の primitive predicate

```lean
def WynerZivCondEntDiffConvex (P_XY : α × β → ℝ) : Prop :=
  ∀ q₁ q₂ : α × β × U → ℝ,
    IsWynerZivFactorizable U P_XY q₁ → IsWynerZivFactorizable U P_XY q₂ →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (wzJointEntYU U (a • q₁ + b • q₂) - wzJointEntXU U (a • q₁ + b • q₂))
        ≤ a * (wzJointEntYU U q₁ - wzJointEntXU U q₁)
          + b * (wzJointEntYU U q₂ - wzJointEntXU U q₂)
```

を **無条件で証明する定理** (`wynerZivCondEntDiffConvex_holds`) を出し、それで
`wynerZivRateFactorizable_convex_in_D_of_condEntDiff` から `h_core` 引数を消した
**unconditional 版** `wynerZivRateFactorizable_convex_in_D`（= L-WZ3 full convexity）を
re-publish する。`lake env lean <file>` clean (0 sorry / 0 warning)、`Common2026.lean` に
import 1 行。

### 完成判定 (この plan が達成すべき 3 点)

1. `wynerZivCondEntDiffConvex_holds (P_XY : α × β → ℝ) (...前提...) : WynerZivCondEntDiffConvex U P_XY`
   — 第一目標は **無条件版** (前提なし)。撤退時のみ `P_XY ≥ 0` or full-support を追加。
2. `wynerZivRateFactorizable_convex_in_D`（unconditional, `h_core` 不要版）の re-publish。
3. `lake env lean Common2026/Shannon/WynerZivCondEntDiffConvexBody.lean` clean + `Common2026.lean` import 追加。

### Approach (解法の全体像 / shape)

凸性の核は `H(m_YU) − H(m_XU)` という **2 つの Shannon block の差**。`negMulLog` は単体で
concave なので `H` 単体の凹性からは差の凸性は出ない。差の凸性 = **joint-convexity-of-relative-entropy**
であり、それを per-atom の `log_sum_inequality_negMulLog` (`Fano/DPI.lean:44`、完全証明済) に
落とすのが要。証明経路は以下の 4 段:

```text
[Step A] affine 翻訳:  m := a•q₁ + b•q₂ の各 marginal は q について affine。
         m_XU(m)(x,u) = a·m_XU(q₁)(x,u) + b·m_XU(q₂)(x,u)   ── wzMarginalXU_smul_add
         m_YU(m)(y,u) = a·m_YU(q₁)(y,u) + b·m_YU(q₂)(y,u)   ── wzMarginalYU_smul_add
         (∑ の中身が q 評価の線形結合 → Finset.sum_add_distrib + Finset.mul_sum)

[Step B] per-u block 凸性 (核):  各 u 固定で、関数
           G_u(q) := (∑_x negMulLog m_XU(q)(x,u)) − (∑_y negMulLog m_YU(q)(y,u))
         の凸性 G_u(m) ≤ a·G_u(q₁) + b·G_u(q₂) を示す。
         これは DPI の per-fiber 集約 (Fano/DPI.lean:203-227) と同型:
         u が fiber index、x が「source」、y が log-sum の atom。
         log_sum_inequality_negMulLog を a-block / b-block の 2 点に当て、
         (negMulLog x + x·log y) ≤ negMulLog(∑x) + (∑x)·log(∑y) を mul_negMulLog_div で
         perspective 形に整え、2-point Jensen に縮約する。

[Step C] ∑_u 集約:  Step B を Finset.sum_le_sum で u 全体に集約。
           ∑_u G_u(m) ≤ ∑_u (a·G_u(q₁) + b·G_u(q₂)) = a·∑_u G_u(q₁) + b·∑_u G_u(q₂).

[Step D] block ↔ joint-ent 同一視:  ∑_u G_u(q) = H(m_YU)(q) − H(m_XU)(q) を
         Fintype.sum_prod_type で (β×U)/(α×U) 上の和に組み替えて wzJointEntYU/XU と一致させ、
         Step C を 主定理の不等式形に linarith / nlinarith で締める。
```

在庫の「想定証明ルート」(`wyner-ziv-convexity-discharge-mathlib-inventory.md:34-46`) の具体化。
**measure 形 (`klDiv : ℝ≥0∞`) の罠を回避する型選択がこの plan の核**: 同じ joint-KL 凸性を
`RateDistortionConvexity.lean:25-26` は measure 形で詰んで ~500 行 gap として hypothesis 化したが、
本 core は **pmf 形 (Real・有限)** なので `log_sum_inequality_negMulLog` がそのまま当たる
(perspective 凸性の一般証明が不要)。**「KL の joint convexity を perspective として一般証明」する
路線を取ると Mathlib 不在で数百行に膨らむ — 必ず per-atom で `log_sum_inequality_negMulLog` を
当てる路線を取ること** (在庫 verdict の警告)。

### `h_ac` (絶対連続性) 充足の戦略 — 第一の難所

`log_sum_inequality_negMulLog` の `h_ac : ∀ i ∈ s, b i = 0 → a i = 0` をどう供給するか。
**Step B で per-u block に当てる際、a/b の選び方が `h_ac` を自明にする鍵**:

- DPI (`Fano/DPI.lean:192-194, 217-220`) では `h_ac` を「`marginal = ∑ over atoms` だから
  `sum=0 → 非負なら各 atom=0` (`Finset.sum_eq_zero_iff_of_nonneg`)」で **無条件に**落としている。
- 本 core でも同型の機会がある: `m_XU(x,u) = ∑_y q(x,y,u)`、`m_YU(y,u) = ∑_x q(x,y,u)` は
  どちらも atom (= `q(x,y,u)`) の有限和。`q ≥ 0` なら sum=0 → 各 atom=0。
- 具体的に Step B の log-sum で `b = `「`a•q₁(·,·,u) + b•q₂(·,·,u)` (= 混合 atom)」、
  `a = `「混合 marginal」を取り、混合 atom=0 → 混合 marginal=0 の向きで `h_ac` を組む。
  混合 atom `a•q₁ + b•q₂` の非負性は `q₁,q₂ ≥ 0` と `a,b ≥ 0` から (`mul_nonneg` + `add_nonneg`)。

**前提リスク**: `q₁,q₂ ≥ 0` を出すには `IsWynerZivFactorizable_nonneg` が `P_XY ≥ 0` (`h_pmf_nn`) を
要求する。`WynerZivCondEntDiffConvex` の signature は `P_XY : α × β → ℝ` のみで pmf 仮定を持たない。

- **第一目標 (無条件版)**: `IsWynerZivFactorizable` から `q ≥ 0` を引き出せるか精査する。
  factorization `q(x,y,u) = κ(u|x)·P_XY(x,y)` で `κ ≥ 0` は出る (`hκnn`) が `P_XY ≥ 0` は別。
  → `WynerZivCondEntDiffConvex` の signature 自体に `P_XY ≥ 0` (or `∈ stdSimplex`) を追加できるかを
  まず確認。predicate の signature 変更は周辺 (`wzObjective_convex_of_condEntDiff`,
  rate wrapper) に波及するが、rate wrapper は既に `h_pmf : P_XY ∈ stdSimplex` を取っている
  (`WynerZivObjectiveConvexityBody.lean:291`) ので、**`P_XY ∈ stdSimplex` を `wynerZivCondEntDiffConvex_holds`
  の前提に追加するのが波及最小の無条件化**。これは「無条件」の譲歩だが、rate wrapper は
  どのみち `h_pmf` を持っているので **rate-level では真に unconditional になる**。
  → **第一目標 = `wynerZivCondEntDiffConvex_holds` を `(h_pmf_nn : ∀ p, 0 ≤ P_XY p)` 1 仮定で証明**。
    これは「core 述語の中身を証明する補題」であって core 述語の def は変えない (def は parameterless のまま)。

- **撤退ライン (最終手段、proof-pivot-advisor 相談後)**: Step B の `h_ac` を `q ≥ 0` から
  落とせない / 混合の絶対連続が破綻するなら、**full-support `P_XY` (`∀ p, 0 < P_XY p`) 追加仮定版**
  `wynerZivCondEntDiffConvex_holds_pos` に縮退して discharge。full support なら混合 atom > 0 (分母正)
  で `h_ac` が自明化し最大の前提リスクが消える。閉包極限での一般化は別補題に後回し。
  **撤退判断は Phase 3 で `h_ac` 充足が崩れた時点で proof-pivot-advisor に相談してから**。

## Phase 0 — 在庫 verdict 確認 + 前提リスク確定 ✅

在庫 (`wyner-ziv-convexity-discharge-mathlib-inventory.md`) が完了済。本 plan で再利用する確定事項:

- [x] core 直撃 Mathlib 補題は 0%（`klDiv` joint convexity / perspective / log-sum すべて Mathlib 不在）。
- [x] 決定打 `log_sum_inequality_negMulLog` (`Fano/DPI.lean:44`, **完全証明済**, 型クラス前提ゼロ)。
- [x] 補助 `mul_negMulLog_div` (`Fano/BinaryJensen.lean:43`, perspective per-atom 変換)。
- [x] 集約テンプレート `condEntropy_le_pushforward_condEntropy` (`Fano/DPI.lean:184-275`、fiber→u block)。
- [x] frame 定義群 (`wzMarginalXU/YU`, `wzJointEntXU/YU`, `IsWynerZivFactorizable`) の位置を確定。
- [x] 前提リスク 4 件: (a) `h_ac` を factorization から落とす, (b) `P_XY ≥ 0` 前提の有無,
      (c) `negMulLog` 定義域 `Ici 0` の `hmem` 供給, (d) `a•q₁+b•q₂` の `Pi` unfold。

**proof-log: no**（在庫 phase。実装なし）

## Phase 1 — skeleton 配置 📋

skeleton-driven (CLAUDE.md)。helper を全て `:= by sorry` で並べ、型検査だけ通す
(LSP `<new-diagnostics>` で sorry warning のみ確認)。import + namespace + section variable も確定。

- [ ] ファイル `Common2026/Shannon/WynerZivCondEntDiffConvexBody.lean` を作成。出だしは在庫 §着手 skeleton
      (`...inventory.md:281-331`) を流用。import:
      `Common2026.Shannon.WynerZivObjectiveConvexityBody` / `Common2026.Fano.DPI` /
      `Common2026.Fano.BinaryJensen` / `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` /
      `Mathlib.Analysis.Convex.Jensen` / `Mathlib.Algebra.BigOperators.Field`。
- [ ] namespace `InformationTheory.Shannon`、section variable
      `{α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]`
      + `(U : Type*) [Fintype U] [MeasurableSpace U]`、`set_option linter.unusedSectionVars false`。
- [ ] 以下 6 helper の statement を `:= by sorry` で配置 (詳細は各 Phase 参照):
      `wzMarginalXU_smul_add` / `wzMarginalYU_smul_add` (Phase 2),
      `wzCondEntDiff_h_ac` (Phase 3, `h_ac` supply),
      `wzCondEntDiff_block_convex` (Phase 4, per-u),
      `wzCondEntDiff_blockSum_eq_jointEntDiff` (Phase 5, block↔joint 同一視),
      `wynerZivCondEntDiffConvex_holds` (Phase 5, 主定理)。
- [ ] `lake env lean Common2026/Shannon/WynerZivCondEntDiffConvexBody.lean` → sorry warning のみで通ること。

**proof-log: no**（skeleton phase）

## Phase 2 — affine 翻訳補題群 📋 (容易, ~30 行)

凸結合の marginal = marginal の凸結合 (Step A)。

- [ ] `wzMarginalXU_smul_add (a b : ℝ) (q₁ q₂ : α × β × U → ℝ) :`
      `wzMarginalXU U (a • q₁ + b • q₂) = a • wzMarginalXU U q₁ + b • wzMarginalXU U q₂`
      — `funext p; unfold wzMarginalXU` → `Pi.add_apply`/`Pi.smul_apply` で被加数を展開 →
      `Finset.sum_add_distrib` + `Finset.mul_sum`。手本: `CsiszarProjection.lean:112`。
- [ ] `wzMarginalYU_smul_add` (YU 版、同型)。
- [ ] **罠**: `a • q₁` は `Pi` の scalar smul なので `(a • q₁) (x,y,u) = a * q₁ (x,y,u)`
      の unfold を忘れると `∑` の中で詰む。`smul_eq_mul` / `Pi.smul_apply` を明示適用。

**proof-log: no**（補題群、軽量）

## Phase 3 — `h_ac` 充足補題 📋 (前提リスク大, ~20–40 行)

第一の難所。Step B の `log_sum_inequality_negMulLog` 適用に必要な絶対連続性
`b i = 0 → a i = 0` を、混合 atom と混合 marginal の構造から供給する。

- [ ] **まず `IsWynerZivFactorizable_nonneg` の前提を精査**: `q ≥ 0` を出すのに `P_XY ≥ 0` が
      要るか確認 (`WynerZivConvexityBody.lean:176`)。要るなら `wynerZivCondEntDiffConvex_holds` の
      前提に `(h_pmf_nn : ∀ p, 0 ≤ P_XY p)` を追加 (Approach の第一目標方針)。
- [ ] `wzCondEntDiff_h_ac` (or per-block inline): 混合 joint `m := a•q₁ + b•q₂` について、
      固定 `u` で `m_XU(m)(x,u) = ∑_y m(x,y,u)`、各 atom `m(x,y,u) ≥ 0` (`q₁,q₂ ≥ 0` + `a,b ≥ 0`)、
      よって `m_XU(m)(x,u) = 0 → ∀ y, m(x,y,u) = 0`
      (`Finset.sum_eq_zero_iff_of_nonneg`)。DPI `:192-194` が直接の手本。
- [ ] **撤退判断点**: ここで「混合の絶対連続が `q ≥ 0` だけから落ちない」「`P_XY ≥ 0` を足しても
      Step B で必要な向きの `h_ac` が組めない」と判明したら、**proof-pivot-advisor に相談**してから
      full-support `P_XY` 版 (`wynerZivCondEntDiffConvex_holds_pos`) に縮退。

**proof-log: yes**（前提事故が起きやすい。`h_ac` の向き・前提追加の判断を残す）

## Phase 4 — per-`u` block 凸性補題 📋 (最大の項, ~80–150 行)

核。固定 `u` で `G_u(m) ≤ a·G_u(q₁) + b·G_u(q₂)` (Step B)。
`log_sum_inequality_negMulLog` を per-u block に当てる。Fano `DPI.lean:203-227` が直接テンプレート。

- [ ] `wzCondEntDiff_block_convex (P_XY) {q₁ q₂} (hq₁ hq₂) (a b ha hb hab) (u : U) :`
      不等式形を確定する。在庫 skeleton は `True` placeholder にしているので、planner として
      **block 不等式形を本 plan で確定**:
      `(∑ x, negMulLog (wzMarginalXU U (a•q₁+b•q₂) (x,u)) - ∑ y, negMulLog (wzMarginalYU U (a•q₁+b•q₂) (y,u)))`
      `≤ a * (∑ x, negMulLog (wzMarginalXU U q₁ (x,u)) - ∑ y, negMulLog (wzMarginalYU U q₁ (y,u)))`
      `+ b * (... q₂ ...)`。
      （符号: `wzJointEntYU - wzJointEntXU = ∑(YU block) - ∑(XU block)` なので block ごとに `YU - XU`。）
- [ ] log-sum を 2 点 (a-block, b-block) に当て `mul_negMulLog_div` で perspective 形に整える。
      `negMulLog` の定義域は `Set.Ici 0`、Jensen `hmem` (= 点が非負) を毎回供給 (`div_nonneg`、Fano `:94` 手本)。
- [ ] Phase 3 の `h_ac` をここで投入。
- [ ] 2-point Jensen に縮約 (重み `a, b`)、`nlinarith` で締める。

**proof-log: yes**（最重量。log-sum 当て方・perspective 整形・Jensen 縮約の判断を残す）

## Phase 5 — `∑_u` 集約 + 主定理 📋 (~30–60 行)

Step C + Step D。per-u を集約し joint-ent 形に組み替えて主定理を締める。

- [ ] `wzCondEntDiff_blockSum_eq_jointEntDiff (q) :`
      `∑ u, (∑ x, negMulLog (wzMarginalXU U q (x,u)) - ∑ y, negMulLog (wzMarginalYU U q (y,u)))`
      `= wzJointEntYU U q - wzJointEntXU U q` (符号注意)。
      `Fintype.sum_prod_type` で `(β×U)` / `(α×U)` 上の和に組み替え。`wzJointEntXU/YU` の def
      (`...Body.lean:78,83`) は `∑ p : α×U / β×U` 形なので、`u` 外側・`x`(or `y`) 内側の二重和に展開して一致。
- [ ] `wynerZivCondEntDiffConvex_holds (P_XY) (h_pmf_nn : ∀ p, 0 ≤ P_XY p) : WynerZivCondEntDiffConvex U P_XY`
      — `intro q₁ q₂ hq₁ hq₂ a b ha hb hab`。Phase 2 の affine 翻訳で marginal を凸結合化、
      Phase 4 を `Finset.sum_le_sum` で u 集約 (Step C)、Phase 5 の同一視で joint-ent 形に戻し、
      `wzMarginalXU_smul_add` 系を使って LHS の `wzJointEntXU/YU (a•q₁+b•q₂)` を展開、`linarith`。
- [ ] **検証**: `lake env lean Common2026/Shannon/WynerZivCondEntDiffConvexBody.lean` clean。

**proof-log: yes**（集約 + 同一視の組み替えで sum-reshape の罠が出やすい）

## Phase 6 — unconditional rate wrapper re-publish 📋 (~15–30 行)

主定理を使い `h_core` 引数を消す。

- [ ] `wynerZivRateFactorizable_convex_in_D` (unconditional 版) を本ファイルで re-publish。
      `WynerZivObjectiveConvexityBody.lean:289` の `_of_condEntDiff` に
      `h_core := wynerZivCondEntDiffConvex_holds U h_pmf.1` (= `P_XY ∈ stdSimplex` から `P_XY ≥ 0`) を
      食わせる。rate wrapper は既に `h_pmf : P_XY ∈ stdSimplex` を取っているので
      **rate-level では真に unconditional** (新規前提なし)。
- [ ] `Common2026.lean` に `import Common2026.Shannon.WynerZivCondEntDiffConvexBody` を 1 行追加。
- [ ] **検証**: `lake env lean` clean + (必要なら) `lake build Common2026.Shannon.WynerZivObjectiveConvexityBody`
      で upstream olean refresh 後に dependent 検証。

**proof-log: no**（wrapper 配線のみ）

## 規模見積もり (在庫 150–300 行の Phase 別按分)

| Phase | 内容 | 行数 |
|---|---|---|
| 1 | skeleton | ~30 |
| 2 | affine 翻訳 (XU/YU) | ~30 |
| 3 | `h_ac` 充足 | ~20–40 |
| 4 | per-u block 凸性 (核) | ~80–150 |
| 5 | ∑_u 集約 + 同一視 + 主定理 | ~30–60 |
| 6 | rate wrapper re-publish | ~15–30 |
| **計** | | **~205–340** |

full-support 縮退時は Phase 3/4 の `h_ac` が自明化し下振れ ~150 行 (在庫 ~120 + wrapper)。

## 依存と検証

- **import 追加**: `Common2026.lean` に `import Common2026.Shannon.WynerZivCondEntDiffConvexBody` 1 行。
- **upstream**: `WynerZivObjectiveConvexityBody` / `Fano.DPI` / `Fano.BinaryJensen` の olean は warm 想定。
  万一 phantom `unknown identifier` が出たら `lake build Common2026.Shannon.WynerZivObjectiveConvexityBody`
  で olean refresh (CLAUDE.md Verification)。
- **検証ポイント**: Phase 1 (skeleton 型検査) / Phase 5 (主定理 clean) / Phase 6 (wrapper + import).
  各点で `lake env lean Common2026/Shannon/WynerZivCondEntDiffConvexBody.lean` が silent (0 sorry / 0 warning)。
- **`lake build` は使わない** (per-fill verifier は `lake env lean`、CLAUDE.md)。

## 撤退ライン

- **第一目標 = 無条件版** (`P_XY ∈ stdSimplex` から取れる `P_XY ≥ 0` のみを `wynerZivCondEntDiffConvex_holds`
  の前提とする。core 述語の def は変えない。rate-level では真に unconditional)。
- **最終手段 (proof-pivot-advisor 相談後)**: Phase 3 で `h_ac` を `q ≥ 0` から落とせない →
  full-support `P_XY` (`∀ p, 0 < P_XY p`) 追加仮定版 `wynerZivCondEntDiffConvex_holds_pos` に縮退。
  full support で分母 > 0 → `h_ac` 自明化。閉包極限の一般化は後回し。
- **絶対に避ける罠** (在庫 verdict 警告): 「KL の joint convexity を perspective として一般証明」する路線。
  Mathlib 不在で数百行に膨らみ `RateDistortionConvexity` の ~500 行 gap を再演する。
  必ず `log_sum_inequality_negMulLog` を per-atom で当てる。
- **既存 signature 変更禁止**: `WynerZivCondEntDiffConvex` の def、`wzObjective_convex_of_condEntDiff`、
  `WynerZivObjectiveConvexityBody.lean` の publish 済 signature は不変。新規 file で独立 publish。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-20 起草**: 在庫 verdict (b) を受け、`log_sum_inequality_negMulLog` per-atom 路線で
   無条件 discharge を第一目標に設定。`P_XY ≥ 0` 前提は rate wrapper が既に `P_XY ∈ stdSimplex` を
   持つことを利用し、core 補題に `h_pmf_nn`/`h_pmf` を渡す形で吸収 (rate-level unconditional)。
   `h_ac` 充足 (Phase 3) を最大リスクと判定し、崩れたら full-support 縮退を撤退ラインに明記。

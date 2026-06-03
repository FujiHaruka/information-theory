# Hoeffding tradeoff (T1-D) ムーンショット計画 🌙

> 実態整合 (2026-05-20): **PASS-THROUGH (sandwich 形)。headline `hoeffding_tradeoff` (unconditional
> Tendsto) は未 publish**。`InformationTheory/Shannon/HoeffdingTradeoff.lean` (0 sorry) に実在するのは
> `hoeffding_tradeoff_with_hypothesis` (:296) で、**achievability (`h_liminf`) と converse (`h_limsup`)
> の両方**を hypothesis として取り (+ 両 boundedness)、本体は `tendsto_of_le_liminf_of_limsup_le` 一行。
> 数学的中身 (liminf ≥ E2 / limsup ≤ E2) は全て pass-through で、Phase C/D は L-H4 で defer のまま。
> Scaffolding は publish 済: `steinTypeII_at_level_pmf` (:115)、`hoeffding_minimizer_ge` (:236,
> Pythagoras 経由)、`hoeffdingE2_minimizer_full_support` (full-support は hypothesis 形)。
> §進捗 Phase C/D の defer 記載は正確だが、§ゴール記載の `hoeffding_tradeoff` 名は実態に無い。

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は ~~取り消し線~~ で残す（完全削除しない、過去参照のため）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
-->

> **Status (2026-05-19)**: 兄弟 plan `chernoff-hoeffding-moonshot-plan.md` で **T1-D Tendsto 形を撤退ライン L-S1 適用で defer**、本 plan に切り出して継続。`hoeffdingE2` 自体の **定義 + min 達成性 + 一意性 + 非負性 + constraint set 凸性** は既に `InformationTheory/Shannon/Chernoff.lean` (1066 行, 0 sorry, library root 編入済) で publish 済。**残るは Tendsto 形主定理 `hoeffding_tradeoff` のみ**。
> **Predecessor**:
> - 在庫 [`hoeffding-tradeoff-mathlib-inventory.md`](hoeffding-tradeoff-mathlib-inventory.md) (~712 行, 既存率 100%, 自作 4-5 種, 中央予測 ~310-410 行)
> - 兄弟 plan [`chernoff-hoeffding-moonshot-plan.md`](chernoff-hoeffding-moonshot-plan.md) §Phase E (L-S1 発動状態、本 plan が継続先)
> **Goal**: Cover-Thomas Theorem 11.7.x の **n-IID Type II at Type I level `alpha` の指数収束 rate = `hoeffdingE2`** を `Tendsto` 形で publish。新規ファイル `InformationTheory/Shannon/HoeffdingTradeoff.lean` (~310-410 行) として独立 publish。
> **撤退ライン**: L-S1 を本 plan に正式 import (兄弟 plan からの継続)、新規 L-H1〜L-H4 (pmf↔Measure bridge / Pythagoras 経由 minimizer / Stein converse `1-ε` 因子 / variational 縮退) + L-HP1〜L-HP3 (自作 plumbing 肥大ライン)。詳細 §撤退ライン。

## 進捗

- [x] Phase 0 — Mathlib + InformationTheory API 在庫 ✅ → [`hoeffding-tradeoff-mathlib-inventory.md`](hoeffding-tradeoff-mathlib-inventory.md)
- [x] Phase 0' — 在庫再確認 + pmf↔Measure bridge 方針確定 (judgement #1: 候補 (a) `PMF.ofFintype` 採用) ✅
- [x] Phase A — skeleton + `steinTypeII_at_level_pmf` 定義 + 基本性質 ✅ (~120 行, 0 sorry)
- [x] Phase B — `hoeffdingConstraintSet_convex` + `hoeffding_minimizer_ge` (Pythagoras 適用) ✅ 🔄 **L-H4 適用**: `hoeffdingE2_minimizer_full_support` (Qstar full-support 反転論証) は **log-singularity gradient 引数** が必要で 30-50 行追加を要し本セッションで discharge 不可 → hypothesis 形 (`hQs_pos` 引数取り) で publish
- [ ] ~~Phase C — achievability `liminf ≥ E_2(α)` (Sanov LDP per-Qstar + acceptance region)~~ 🔄 **L-H4 適用**: defer 別 plan へ
- [ ] ~~Phase D — converse `limsup ≤ E_2(α)` (Stein typicality template + Pythagoras)~~ 🔄 **L-H4 適用**: defer 別 plan へ
- [x] Phase E — 主定理 wrapper `hoeffding_tradeoff_with_hypothesis` (sandwich Tendsto, hypothesis 形) ✅
- [ ] Phase V — verify + `InformationTheory.lean` 編入 (オーケストレータ側) 📋

## ゴール / Approach

### 最終到達点

新規ファイル `InformationTheory/Shannon/HoeffdingTradeoff.lean` で主定理 publish:

```lean
namespace InformationTheory.Shannon.HoeffdingTradeoff

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- n-IID Type II error of the optimal level-`alpha` test (pmf 形). -/
noncomputable def steinBetaSet_pmf (P₁ P₂ : α → ℝ) (n : ℕ) (alpha : ℝ) : Set ℝ :=
  { β : ℝ | ∃ (s : Finset (Fin n → α)),
      (1 - ∑ x ∈ s, ∏ i, P₁ (x i)) ≤ alpha ∧
      β = ∑ x ∈ s, ∏ i, P₂ (x i) }

noncomputable def steinTypeII_at_level_pmf (P₁ P₂ : α → ℝ) (n : ℕ) (alpha : ℝ) : ℝ :=
  sInf (steinBetaSet_pmf P₁ P₂ n alpha)

/-- **Hoeffding tradeoff lemma** (Cover-Thomas Theorem 11.7.x). -/
theorem hoeffding_tradeoff
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : (∑ a, P₁ a) = 1) (hP₂_sum : (∑ a, P₂ a) = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂) :
    Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha))
```

(`hoeffdingE2` / `hoeffdingE2_attained` / `hoeffdingE2_unique` / `hoeffdingE2_nonneg` /
`hoeffdingConstraintSet` family は **既に `InformationTheory/Shannon/Chernoff.lean` で publish 済** — 本 plan ではそのまま import して使う。)

判断ログ #1 で **statement 形 (`Tendsto` 直書き vs `DotEq` corollary)** を確定する。
現時点では InformationTheory 既存スタイル (`stein_lemma`, `chernoff_lemma_achievability`, `sanov_ldp_equality`)
に揃えて `Tendsto` 直書きを main、`DotEq` 形は `dotEq_iff_tendsto_log_div` (`Asymptotic.lean:116`)
経由の corollary に下ろす方針 (兄弟 plan 判断ログ #1 と同 style)。

### Approach (中核 4 ピース)

**Mathlib-shape-driven** で textbook の `min_{Q : D(Q‖P₁) ≤ α} D(Q‖P₂)` を直書きせず、
**既存 InformationTheory plumbing (Csiszar projection / Sanov LDP equality / Stein typicality template) の
結論形に合わせて** Qstar 経由で n-IID 化する。

1. **`steinTypeII_at_level_pmf` を `Stein.steinBetaSet` (Measure 経路) の pmf-mirror で定義**:
   - `steinBetaSet_pmf P₁ P₂ n alpha := { β | ∃ s : Finset (Fin n → α), (1 - ∑_s P₁^n) ≤ α ∧ β = ∑_s P₂^n }`
   - **設計選択の根拠** (CLAUDE.md §「Mathlib-shape-driven Definitions」): `steinBetaSet` (`Stein.lean:1139`)
     の構造をそのまま pmf 形に転写すれば、`Stein.lean` の per-ε achievability/converse template
     (`steinTypicalSet_Q_prob_le`, `steinOptimalBeta_log_le_of_converse`,
     `steinOptimalBeta_log_ge_of_achievability`) が **Qstar 置換だけで** 流用できる。

2. **Qstar minimizer 性は Csiszar projection + Pythagoras で整理**:
   - `hoeffdingE2_attained` (`Chernoff.lean:310`) から `Qstar ∈ hoeffdingConstraintSet P₁ alpha` と
     `hoeffdingE2 = klDivPmf Qstar P₂` を取り出す
   - **Qstar full-support 性** (`∀ a, 0 < Qstar a`) は `hoeffdingE2_attained` から自動では出ない —
     `csiszar_pythagoras_inequality` (`CsiszarProjection.lean:449`) が `hQs_pos` を verbatim で要求するので
     **`hoeffdingE2_minimizer_full_support` 補題を新規** に書く (KL strict convexity + 反転論証, ~30-50 行)
   - `csiszar_pythagoras_inequality` で `K := hoeffdingConstraintSet`, `Q := P₂`, `P := (c/n : α → ℝ)` を取れば
     `klDivPmf (c/n) P₂ ≥ klDivPmf (c/n) Qstar + klDivPmf Qstar P₂` (Cover-Thomas 11.6.1 の本質)

3. **Sanov LDP per-Qstar 起動** (`Q := P₂_meas`, `P := Qstar`):
   - `sanov_ldp_equality` (`SanovLDPEquality.lean:1243`) を Qstar 周辺の type class neighborhood
     `E_n^* := {c | (c/n) ∈ hoeffdingConstraintSet P₁ alpha}` で起動 → `(1/n) log P₂^n(⋃_{c ∈ E_n^*} typeClassByCount c) → -klDivPmf Qstar P₂ = -E_2(α)`
   - `h_minimizer` 仮定 (`klDivSumForm_ofVec Qstar (P₂.real ∘ ·) ≤ klDivIndex c n P₂_meas` per `c ∈ E_n^*`)
     は **Pythagoras 経由で自動成立** — `klDivPmf (c/n) Qstar ≥ 0` から `klDivPmf (c/n) P₂ ≥ klDivPmf Qstar P₂` ⇒
     sum-form bridge で `klDivIndex c n P₂_meas ≥ klDivSumForm_ofVec Qstar (P₂.real ∘ ·)`
   - **pmf ↔ Measure bridge** は `pmfToMeasure : (α → ℝ) → Measure α` (新規 helper, ~20-30 行)
     で 1 本化 (judgement #1 で確定)

4. **Achievability + Converse の sandwich**:
   - **Achievability** (Phase C, `liminf ≥ E_2(α)`): acceptance region `s_n := ⋃_{c ∈ E_n^*} typeClassByCount c` を取り、
     - Type I 制御 (`P₁^n s_n ≥ 1 - alpha`): Qstar ∈ K より `P₁^n` 質量が K 周辺の type に集中 (Sanov LDP for `P := P₁, Q := P₁` の AEP 版、補助補題 `p_n_typeclass_tendsto_one`)
     - Type II 上限 (`P₂^n s_n ≤ exp(-n · (E_2(α) - δ))`): Sanov LDP per-Qstar 起動の直接帰結
   - **Converse** (Phase D, `limsup ≤ E_2(α)`): Stein typicality template `steinTypicalSet_Q_prob_le` の
     **Qstar 流用** (Qstar = P, P₂ = Q として読み替え) + Pythagoras で「Qstar が `K` 内の hardest-to-distinguish Q」を立証 → 任意の test で Type II 下界
   - sandwich → `tendsto_of_le_liminf_of_limsup_le` で Tendsto

### Approach 図

```
Phase 0   : 在庫 (既存) + Phase 0' で pmf↔Measure 方針確定          ← 完了済 + 判断 1 ターン
            ────────────────────────────────────────────────
Phase A   : skeleton + steinTypeII_at_level_pmf 定義 + 基本性質      ← 0.5 セッション (60-80 行)
Phase B   : hoeffdingE2_minimizer_full_support (Qstar > 0)          ← 0.5 セッション (30-50 行)
Phase C   : Achievability (Sanov LDP per-Qstar + acceptance region)  ← 1.0 セッション (80-120 行)
            ←──── 撤退ライン L-H4 (variational expression 縮退) ────→
Phase D   : Converse (Stein typicality template + Pythagoras)       ← 1.0 セッション (60-100 行)
Phase E   : 主定理 wrapper hoeffding_tradeoff (sandwich Tendsto)    ← 0.25 セッション (20-30 行)
Phase V   : verify + InformationTheory.lean 編入 (オーケストレータ)         ← 5 分
```

### 規模見積 (再掲, 在庫より)

- skeleton + imports + namespace + docstring: ~40-60 行
- 自作 1 (`steinTypeII_at_level_pmf` 定義 + 基本性質 + pmf↔Measure bridge): ~60 行
- 自作 2 (Qstar full-support + minimizer 整理): ~50-70 行
- 自作 3 (Achievability, Sanov LDP per-Qstar): ~120-150 行
- 自作 4 (Converse, Stein typicality 流用): ~60-100 行
- 自作 5 (主定理 wrapper sandwich): ~20-30 行
- **合計**: ~310-410 行 (在庫 §「Phase X で使う API のうち N% が Mathlib に既存」の中央予測と整合)
- **想定セッション数**: ~3-4 セッション (Phase A+B → C → D → E)

### ファイル構成 (Phase V 完了想定)

```
InformationTheory/Shannon/
  HoeffdingTradeoff.lean     ← 新規 (本 plan の publish 先, ~310-410 行)
  Chernoff.lean              ← 既存 1066 行 (hoeffdingE2 family を提供, 変更なし)
  Stein.lean                 ← 既存 1481 行 (steinBetaSet / steinTypicalSet template, 変更なし)
  StrongStein.lean           ← 既存 641 行 (strict Tendsto 形, 変更なし)
  SanovLDPEquality.lean      ← 既存 1243 行 (sanov_ldp_equality, 変更なし)
  CsiszarProjection.lean     ← 既存 487 行 (klDivPmf + Pythagoras, 変更なし)
  KLDivContinuous.lean       ← 既存 (klDivSumForm_ofVec, 変更なし)
InformationTheory/InformationTheory/
  Asymptotic.lean            ← 既存 (DotEq notation, 変更なし)
InformationTheory.lean              ← `import InformationTheory.Shannon.HoeffdingTradeoff` を追記 (Phase V, オーケストレータ)
```

**`Chernoff.lean` 末尾追記は採用しない**: 既存 1066 行に Tendsto 形 + Sanov LDP per-Qstar plumbing を
追記すると scope が散らかる (Chernoff achievability + Hoeffding variational + Hoeffding tradeoff の
3 主題が 1 ファイルに混在)。新規ファイル `HoeffdingTradeoff.lean` 採用 — 主題が「T1-D Tendsto 形のみ」
で閉じる + import で `Chernoff.lean` 既存定義を再利用するのが clean。

## 依存関係

完了済 (再利用可):

- [x] `InformationTheory/Shannon/Chernoff.lean` (1066 行, 0 sorry)
  - `hoeffdingE2`, `hoeffdingE2_attained`, `hoeffdingE2_unique`, `hoeffdingE2_nonneg`
  - `hoeffdingConstraintSet`, `hoeffdingConstraintSet_isClosed`, `hoeffdingConstraintSet_nonempty`,
    `hoeffdingConstraintSet_subset_stdSimplex`
  - `klDivPmf_self_eq_zero`
- [x] `InformationTheory/Shannon/CsiszarProjection.lean` (487 行)
  - `klDivPmf`, `continuous_klDivPmf_left`, `klDivPmf_strictConvexOn_left`, `klDivPmf_nonneg`
  - `isCompact_of_subset_stdSimplex`
  - `csiszar_projection_exists`, `csiszar_projection_unique`
  - **`csiszar_pythagoras_inequality`** (本 plan の Phase B/C/D の主機械)
  - `klDivPmf_eq_log_diff_sum`
- [x] `InformationTheory/Shannon/Stein.lean` (1481 行)
  - `llrPmf`, `logLikelihoodRatio`
  - **`steinTypicalSet`, `steinTypicalSet_P_prob_tendsto_one`, `steinTypicalSet_Q_prob_le`** (Phase D template)
  - `stein_achievability` (Phase C template)
  - `klDiv_pi_eq_n_smul`
  - `steinBetaSet`, `steinOptimalBeta`, `exp_le_steinOptimalBeta`,
    `steinOptimalBeta_log_le_of_converse`, `steinOptimalBeta_log_ge_of_achievability`,
    `stein_lemma`
- [x] `InformationTheory/Shannon/StrongStein.lean` (641 行)
  - `stein_strong_lemma` (Phase D で Stein 標準形の `1 - ε` 因子を回避するための代替路)
- [x] `InformationTheory/Shannon/SanovLDPEquality.lean` (1243 行)
  - `TypeCountIndex`, `typeClassByCount`, `klDivIndex`, `roundedTypeIndex`
  - **`sanov_ldp_equality`** (本 plan の Phase C/E の主機械)
- [x] `InformationTheory/Shannon/KLDivContinuous.lean`
  - `klDivSumForm_ofVec` (Csiszar `klDivPmf` ↔ Sanov `klDivIndex` の bridge primitive)
- [x] `InformationTheory/InformationTheory/Asymptotic.lean`
  - `DotEq`, `dotEq_iff_tendsto_log_div`, `exp_decay_N_of_pos`
- [x] Mathlib `Measure.tilted` family, `LogLikelihoodRatio` family, `KullbackLeibler` family,
  `Probability.ProbabilityMassFunction.Basic` (`PMF.toMeasure`),
  `Topology.Order.LiminfLimsup` (`tendsto_of_le_liminf_of_limsup_le`)

---

## Phase 0 — Mathlib + InformationTheory API 在庫 ✅

完了 (`docs/shannon/hoeffding-tradeoff-mathlib-inventory.md`, 712 行)。

主結論 (在庫 §まとめ より):

- **既存 API カバレッジ 100%** (実体ベース ~30 項目): Sanov LDP equality + Stein achievability/converse template + Csiszar projection + Pythagoras が全て揃っている
- **自作 4-5 種**: `steinTypeII_at_level_pmf` / `hoeffding_sanov_minimizer` / `hoeffding_tradeoff_achievability` / `hoeffding_tradeoff_converse` / `hoeffding_tradeoff`
- **規模見積**: ~310-410 行 (中央 350 行)
- **撤退ライン L-S1** (兄弟 plan で発動済) を本 plan に正式 import
- **最大 risk**: Qstar full-support 性 (Phase B の核補題) — `csiszar_pythagoras_inequality` の `hQs_pos`
  要件を満たすために新規補題 ~30-50 行が必要、見落とすと Phase C/D/E 全て破綻

---

## Phase 0' — 在庫再確認 + pmf↔Measure bridge 方針確定 📋

### スコープ

実装着手前の judgement ターン (1 セッションの 0.1 程度)。在庫 §危険箇所 3 (pmf↔Measure bridge 方針) を
**Phase A 着手前に確定** することで Phase C/D の plumbing 規模を ±100 行レンジで予測可能にする。

### Done 条件

- 判断ログ #1 に「pmf↔Measure bridge を (a) 全部書く / (b) pmf 形で全部書く / (c) 中間案 のどれを取るか」を append
- 在庫 §「自作必要な要素」§自作 1〜5 を再読、各自作項目の signature を最終確定 (Phase A skeleton に反映)
- (任意) loogle で `PMF.toMeasure_apply` + `PMF.ofFintype` 系の Mathlib API 存在を再確認

### ステップ

- [ ] **0'-1 在庫再読**: `hoeffding-tradeoff-mathlib-inventory.md` §「自作が必要な要素」§「重要な前提条件」§「主要発見 (危険な点)」を流し読み。特に §危険 1 (Qstar full-support) と §危険 3 (pmf↔Measure bridge) を確認

- [ ] **0'-2 pmf↔Measure bridge 方針確定** (judgement #1):
  - 候補 (a): `pmfToMeasure (P : α → ℝ) (hP_nn) (hP_sum) : Measure α := PMF.toMeasure (PMF.ofFintype P hP_nn hP_sum)` + `pmfToMeasure_real_singleton`, `pmfToMeasure_isProbabilityMeasure`, `pmfToMeasure_pos` の 3 補題 (~30 行)
  - 候補 (b): pmf 形 Sanov LDP の **自前 reimplementation** (~80-120 行)、Measure 経由を一切経由しない
  - 候補 (c): Sanov LDP のみ Measure 経路に上げ、Stein typicality template も Measure 経路で起動、最終 `hoeffding_tradeoff` の statement のみ pmf 形 (~50 行 bridge)
  - **推奨**: 候補 (a) — Mathlib `PMF.ofFintype` + `PMF.toMeasure` の既存補題で ~30 行に収まる + Phase C で Sanov LDP per-Qstar 起動時に `Q := pmfToMeasure P₂` で済む
  - **撤退ライン L-H1**: bridge plumbing が 50 行を超えたら候補 (b) または (c) にピボット

- [ ] **0'-3 Phase A skeleton 設計の最終確定**:
  - 在庫 §着手 skeleton (~150 行, line 454-645) をベースに、判断 #1 の bridge 方針に合わせて signature 微調整
  - 各 Phase の `:= by sorry` 並びを最終化、Phase A で Write する skeleton の line 数を見積もり

### 工数感

~30 分 (判断 1 ターン)。proof-log `no` (実装着手前の判断のみ)。

### 失敗時 fallback

- 判断 #1 で候補 (a) を取った後 Phase A で bridge plumbing が 50 行を超えそうな兆候 (`pmfToMeasure` の measurability で `[MeasurableSingletonClass α]` 不足、`PMF.ofFintype` の signature 不一致) があれば、Phase A 着手の早期に候補 (c) (Measure 経路統一) にピボット

---

## Phase A — skeleton + `steinTypeII_at_level_pmf` 定義 + 基本性質 📋

### スコープ

新規ファイル `InformationTheory/Shannon/HoeffdingTradeoff.lean` の skeleton (全主定理 + 補助補題を
`:= by sorry` で並べた状態) を Write、LSP 診断で type-check OK 確認 → `steinBetaSet_pmf` /
`steinTypeII_at_level_pmf` 定義 + 基本性質を fill in。

### Done 条件

- `InformationTheory/Shannon/HoeffdingTradeoff.lean` skeleton (~150-200 行, sorry 多数) が `lake env lean` で
  type-check OK (sorry 警告のみ、エラーなし)
- `steinBetaSet_pmf`, `steinTypeII_at_level_pmf` 定義 + 以下の基本性質補題が 0 sorry:
  - `one_mem_steinBetaSet_pmf` (test = univ で β = 1 が常に達成可能)
  - `steinBetaSet_pmf_bddBelow` (β ≥ 0)
  - `steinTypeII_at_level_pmf_nonneg` (`0 ≤ steinTypeII_at_level_pmf`)
- pmf↔Measure bridge (`pmfToMeasure` + 3 補題) が 0 sorry
- Phase B-E は `:= by sorry` のまま

### ステップ

- [ ] **A-0 skeleton Write** (CLAUDE.md §「Skeleton-driven Development」):
  - 在庫 §着手 skeleton (line 454-645) をテンプレに、判断 #1 の bridge 方針を反映して Write
  - import 行: `InformationTheory.Shannon.Chernoff` / `Stein` / `StrongStein` / `SanovLDPEquality` /
    `CsiszarProjection` / `KLDivContinuous` / `InformationTheory.InformationTheory.Asymptotic` /
    `Mathlib.Probability.ProbabilityMassFunction.{Basic,Constructions}` /
    `Mathlib.Topology.Order.{LiminfLimsup,Compact}`
  - namespace: `InformationTheory.Shannon.HoeffdingTradeoff`
  - `set_option linter.unusedSectionVars false`
  - LSP 診断で sorry 警告のみ確認

- [ ] **A-1 pmf↔Measure bridge** (判断 #1 の候補 (a) の場合):

  ```lean
  noncomputable def pmfToMeasure (P : α → ℝ)
      (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1) : Measure α :=
    -- PMF.ofFintype + PMF.toMeasure
    sorry

  instance pmfToMeasure_isProbabilityMeasure
      (P : α → ℝ) (hP_nn) (hP_sum) :
      IsProbabilityMeasure (pmfToMeasure P hP_nn hP_sum) := by sorry

  lemma pmfToMeasure_real_singleton
      (P : α → ℝ) (hP_nn) (hP_sum) (a : α) :
      (pmfToMeasure P hP_nn hP_sum).real {a} = P a := by sorry

  lemma pmfToMeasure_pos
      (P : α → ℝ) (hP_pos : ∀ a, 0 < P a) (hP_sum : ∑ a, P a = 1) (a : α) :
      0 < (pmfToMeasure P (fun a => (hP_pos a).le) hP_sum).real {a} := by sorry
  ```

- [ ] **A-2 `steinBetaSet_pmf` / `steinTypeII_at_level_pmf` 定義**:

  ```lean
  noncomputable def steinBetaSet_pmf (P₁ P₂ : α → ℝ) (n : ℕ) (alpha : ℝ) : Set ℝ :=
    { β : ℝ | ∃ (s : Finset (Fin n → α)),
        (1 - ∑ x ∈ s, ∏ i, P₁ (x i)) ≤ alpha ∧
        β = ∑ x ∈ s, ∏ i, P₂ (x i) }

  noncomputable def steinTypeII_at_level_pmf (P₁ P₂ : α → ℝ) (n : ℕ) (alpha : ℝ) : ℝ :=
    sInf (steinBetaSet_pmf P₁ P₂ n alpha)
  ```

  Convention: `s` は **acceptance region for H₀** (test が "accept H₀" を返す sample 集合)、
  Stein.lean `steinBetaSet` (Stein.lean:1139) と一致。Type I = `P₁^n sᶜ` (probability of false-reject),
  Type II = `P₂^n s` (probability of false-accept)。

- [ ] **A-3 `one_mem_steinBetaSet_pmf`**:

  ```lean
  lemma one_mem_steinBetaSet_pmf
      (P₁ P₂ : α → ℝ) (hP₂_sum : ∑ a, P₂ a = 1)
      (n : ℕ) (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) :
      (1 : ℝ) ∈ steinBetaSet_pmf P₁ P₂ n alpha
  ```

  - `s := (Finset.univ : Finset (Fin n → α))` で `1 - ∑ P₁^n = 0 ≤ alpha`、`∑ P₂^n = 1`
  - `∑ P₂^n = 1` は `Finset.prod_sum_eq_sum_pi` 系 (Fintype.piFinset_univ) で `(∑ a, P₂ a)^n = 1^n = 1`

- [ ] **A-4 `steinBetaSet_pmf_bddBelow`**:

  ```lean
  lemma steinBetaSet_pmf_bddBelow
      (P₁ P₂ : α → ℝ) (hP₂_nn : ∀ a, 0 ≤ P₂ a) (n : ℕ) (alpha : ℝ) :
      BddBelow (steinBetaSet_pmf P₁ P₂ n alpha)
  ```

  - 任意の `s` で `∑_s ∏ P₂ ≥ 0` (Finset.sum_nonneg + Finset.prod_nonneg)

- [ ] **A-5 `steinTypeII_at_level_pmf_nonneg`**:

  ```lean
  lemma steinTypeII_at_level_pmf_nonneg
      (P₁ P₂ : α → ℝ) (hP₂_nn : ∀ a, 0 ≤ P₂ a) (n : ℕ) (alpha : ℝ) :
      0 ≤ steinTypeII_at_level_pmf P₁ P₂ n alpha
  ```

  - A-4 から `Real.sInf_le_iff` (BddBelow + nonempty で `0 ≤ sInf S ↔ ∀ a ∈ S, 0 ≤ a`)

### 工数感

~100-150 行 (skeleton ~80 行 + A-1〜A-5 ~30-50 行)。proof-log `no` (skeleton の標準的 plumbing)。

### 失敗時 fallback

- **A-1 bridge plumbing が 50 行を超える**: L-H1 発動 → 判断 #1 を Phase 0' で候補 (c) (Measure 経路統一) に
  ピボット。再び skeleton 設計に戻す
- **A-3 `one_mem_steinBetaSet_pmf` の `∑ P₂^n = 1` で `Fintype.piFinset_univ` の sum reshape が
  Mathlib に直接補題なし**: `Finset.prod_sum_eq_sum_pi` の variant を自前で書く (~10 行)、または
  `Finset.prod_pow_eq_pow_sum` 経由

---

## Phase B — `hoeffdingE2_minimizer_full_support` (Qstar > 0) 📋

### スコープ

`hoeffdingE2_attained` (`Chernoff.lean:310`) から取り出される `Qstar ∈ hoeffdingConstraintSet P₁ alpha`
が `Qstar ∈ stdSimplex` (`∀ a, 0 ≤ Qstar a`) しか保証しないことに対し、**Qstar が `K` 内の minimizer
である限り `∀ a, 0 < Qstar a`** を示す補題を publish。
これは `csiszar_pythagoras_inequality` (Phase C/D で使用) の `hQs_pos` 要件を満たすために必須。

### Done 条件

- `hoeffdingE2_minimizer_full_support : ∀ a, 0 < Qstar a` (0 sorry)
- 任意で `hoeffdingConstraintSet_convex` を **公開 lemma** として切り出し (在庫 §自作 6, Chernoff.lean:585
  内部で実質展開済の helper を本 plan で publish 化)

### ステップ

- [ ] **B-1 `hoeffdingConstraintSet_convex`** (在庫 §自作 6):

  ```lean
  lemma hoeffdingConstraintSet_convex
      (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (alpha : ℝ) :
      Convex ℝ (hoeffdingConstraintSet P₁ alpha)
  ```

  - `K = stdSimplex ℝ α ∩ {Q | klDivPmf Q P₁ ≤ alpha}`
  - 各々が凸: `convex_stdSimplex` (Mathlib) + `klDivPmf_strictConvexOn_left.convexOn.convex_le` (`{Q | f Q ≤ c}` is convex when `f` is convex)
  - intersection も凸: `Convex.inter`
  - **既に Chernoff.lean:585 `hoeffdingE2_unique` 内部で local に展開済** (~10 行) → 公開 lemma に切り出し ~5 行

- [ ] **B-2 `hoeffdingE2_minimizer_full_support`**:

  ```lean
  lemma hoeffdingE2_minimizer_full_support
      (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
      (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
      (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂)
      {Qstar : α → ℝ}
      (hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha)
      (hQs_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂) :
      ∀ a, 0 < Qstar a
  ```

  **戦略** (在庫 §危険 1 + §自作 2 落とし穴 2):
  1. 仮定: ある `a₀ : α` で `Qstar a₀ = 0`
  2. `Qstar' := (1 - ε) • Qstar + ε • P₁` (`ε > 0` 小) を取る
     - `Qstar' ∈ stdSimplex` (`stdSimplex.smul_add` + 凸性)
     - `Qstar' a₀ = ε · P₁ a₀ > 0` (`P₁ a₀ > 0` から)、つまり Qstar より strict に小さい klDivPmf
  3. **`klDivPmf Qstar' P₁ ≤ alpha`** (凸結合で `klDivPmf P₁ P₁ = 0` を混ぜているので、
     KL の `K` 凸性 + `klDivPmf P₁ P₁ = 0 ≤ alpha` から `Qstar' ∈ K`)
  4. **`klDivPmf Qstar' P₂ < klDivPmf Qstar P₂`**: KL strict convexity (`klDivPmf_strictConvexOn_left`)
     + `Qstar ≠ P₁` (`h_alpha_lt : alpha < klDivPmf P₁ P₂` から `P₁ ∉` 内部 minimizer に該当する K 上限点なので Qstar ≠ P₁)
  5. これは `hQs_min : hoeffdingE2 = klDivPmf Qstar P₂` (Qstar が `K` 上の minimizer) に矛盾
  6. ∴ `∀ a, Qstar a ≠ 0`、組み合わせて `0 < Qstar a` (Qstar ∈ stdSimplex で `0 ≤ Qstar a` だから)

  **実装上の注意**:
  - step 4 の strict convexity の使い方は微妙: `klDivPmf · P₂` は K 上で strict convex なので、
    K 内の **任意の 2 点の midpoint** が strict に小さい値を取る。`Qstar a₀ = 0` を反転として直接 0 を
    超える `Qstar'` を作る (ε perturbation で full-support 化) ⇒ 矛盾
  - **`h_alpha_lt : alpha < klDivPmf P₁ P₂` が必要**: もし `alpha = klDivPmf P₁ P₂` なら `Qstar = P₂` が
    達成可能 (alpha = D(P₂‖P₁) ≥ alpha) で、`Qstar = P₂` は `hP₂_pos` から full-support 確定。
    `alpha < D(P₁‖P₂)` の場合のみ Qstar が `P₂` でない可能性があるが、いずれにせよ K 内の minimizer は full-support

### 工数感

~30-50 行 (B-1 ~5 行 + B-2 ~25-45 行)。proof-log `yes` (反転論証 + strict convexity の細部が微妙)。

### 失敗時 fallback

- **B-2 の反転論証で `Qstar' ∈ K` の確認が肥大** (KL の凸結合の `≤` 不等式が微妙):
  代替路として `klDivPmf · P₂` の minimizer 性を **`csiszar_projection_unique`** で立証 → Csiszar projection
  の **既存 full-support 保証** (`csiszar_projection_exists` の結論で出る Qstar は full-support か?
  → 在庫で要確認、もし出ているなら B-2 は trivial)
- **代替**: `hoeffdingE2_attained` の証明を再読し、内部で Qstar full-support が暗黙に成立している
  なら直接そこから抽出可能 (Chernoff.lean:310-339 の証明を確認)

---

## Phase C — Achievability `liminf ≥ E_2(α)` 📋

### スコープ

acceptance region `s_n := ⋃_{c ∈ E_n^*} typeClassByCount c` (E_n^* := `K` 周辺の type 全部) を構築し、
Sanov LDP per-Qstar 起動で **`liminf -((1:ℝ)/n) log (steinTypeII_at_level_pmf P₁ P₂ n alpha) ≥ E_2(α)`**
を確定。

### Done 条件

- `hoeffding_tradeoff_achievability` (0 sorry):

  ```lean
  theorem hoeffding_tradeoff_achievability
      (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
      (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
      (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂)
      {δ : ℝ} (hδ : 0 < δ) :
      ∀ᶠ n : ℕ in atTop, ∃ s : Finset (Fin n → α),
        (1 - ∑ x ∈ s, ∏ i, P₁ (x i)) ≤ alpha ∧
        hoeffdingE2 P₁ P₂ alpha - δ ≤
          -((1 : ℝ) / n) * Real.log (∑ x ∈ s, ∏ i, P₂ (x i))
  ```

### ステップ

- [ ] **C-1 Qstar 取り出し**:
  - `obtain ⟨Qstar, hQs_mem, hQs_min⟩ := hoeffdingE2_attained P₁ P₂ hP₁_pos hP₂_pos hP₁_sum alpha h_alpha_nn`
  - `have hQs_pos : ∀ a, 0 < Qstar a := hoeffdingE2_minimizer_full_support ... hQs_mem hQs_min` (Phase B)

- [ ] **C-2 `hoeffding_sanov_minimizer` 補助補題** (在庫 §自作 2):

  ```lean
  lemma hoeffding_sanov_minimizer
      (P₁ P₂ : α → ℝ) (hP₁_pos hP₂_pos hP₁_sum hP₂_sum)
      (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha)
      {Qstar : α → ℝ}
      (hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha)
      (hQs_pos : ∀ a, 0 < Qstar a)
      (hQs_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂)
      (n : ℕ) (c : α → ℕ)
      (hc_in_K : (fun a => (c a : ℝ) / n) ∈ hoeffdingConstraintSet P₁ alpha) :
      klDivSumForm_ofVec Qstar P₂
        ≤ klDivIndex c n (pmfToMeasure P₂ ...)
  ```

  **戦略**:
  1. `csiszar_pythagoras_inequality` を適用 (`K := hoeffdingConstraintSet`, `Q := P₂`, `Qstar := Qstar`,
     `P := (c/n : α → ℝ)`): `klDivPmf (c/n) P₂ ≥ klDivPmf (c/n) Qstar + klDivPmf Qstar P₂`
  2. `klDivPmf (c/n) Qstar ≥ 0` (`klDivPmf_nonneg`)
  3. ∴ `klDivPmf (c/n) P₂ ≥ klDivPmf Qstar P₂`
  4. sum-form bridge (`klDivPmf_eq_log_diff_sum` ~~+ `klDivSumForm_ofVec` ↔ `klDivIndex`~~ で
     `klDivPmf (c/n) P₂ = klDivIndex c n P₂_meas` + `klDivPmf Qstar P₂ = klDivSumForm_ofVec Qstar P₂`)
  5. 合成で `klDivSumForm_ofVec Qstar P₂ ≤ klDivIndex c n P₂_meas`

- [ ] **C-3 acceptance region `E_n^*` 構築**:
  - `E_n^* := (Finset.univ : Finset (TypeCountIndex α n)).filter (fun c => (fun a => (c a : ℝ) / n) ∈ hoeffdingConstraintSet P₁ alpha)`
  - **Decidable 性**: `hoeffdingConstraintSet P₁ alpha` の membership が decidable か → `klDivPmf · P₁ ≤ alpha` の decidable 性は `Real` 上では構造的に出ないので **`Classical.dec` で済ます** (`classical attribute`)
  - 在庫 §危険 2 で警告された plumbing が ~30-50 行ここで集約

- [ ] **C-4 Sanov LDP per-Qstar 起動** (`sanov_ldp_equality` を `Q := pmfToMeasure P₂`, `P := Qstar` で):
  - `h_in_E : ∀ᶠ n in atTop, roundedTypeIndex Qstar n ∈ E_n^*` — `roundedTypeIndex Qstar n` は近似的に `Qstar` を表現する type、`Qstar ∈ K` から (rounding 誤差をクリアできる程度に) `(roundedTypeIndex Qstar n / n) ∈ K`
  - `h_minimizer : ∀ n, ∀ c ∈ E_n^*, klDivSumForm_ofVec Qstar P₂ ≤ klDivIndex c n P₂_meas` — C-2 から直接
  - 結論: `Tendsto (fun n => (1/n) * log (P₂^n (⋃_{c ∈ E_n^*} typeClassByCount c))) atTop (𝓝 (-klDivSumForm_ofVec Qstar P₂))`
  - sum-form bridge で `klDivSumForm_ofVec Qstar P₂ = klDivPmf Qstar P₂ = hoeffdingE2 P₁ P₂ alpha`

- [ ] **C-5 Type I 制御**: `∀ᶠ n in atTop, P₁^n (⋃_{c ∈ E_n^*} typeClassByCount c) ≥ 1 - alpha`
  - **方針 1** (Sanov LDP for `P := P₁, Q := P₁` 自己呼び出し): `klDivPmf P₁ P₁ = 0` から typeClass が `P₁` 周辺に集中 (大数の法則 AEP 版)、`E_n^*` は `Qstar` 周辺だが `Qstar ∈ K` で `D(Qstar‖P₁) ≤ alpha` だから `P₁^n(E_n^*) ≥ ?` で `≥ 1 - alpha` の直接導出は微妙
  - **方針 2** (より素直): typeClass が `K` 全体をカバーするので、`P₁^n` の type が `K` 内に入る確率が `→ 1`、その上で
    `P₁^n((⋃_{c ∈ K_n} T_c)^c) ≤ exp(-n · D(K^c, P₁))` の Sanov 下界 (`D(K^c, P₁) ≥ alpha` なら Type I → alpha 以下)
  - **実装上の判定**: 在庫 §危険 5 (Type I 制御の Sanov LDP for `P := P₁, Q := P₁` 自己呼び出し) で
    指摘されたが、本質的に AEP 版を**自前で書く方が短い可能性大** (~30-40 行、補助補題 `p_n_typeclass_tendsto_one`)。
    Phase C 着手時に判定

- [ ] **C-6 Type II 上限 + δ-loose**: C-4 の結論 `(1/n) log P₂^n(⋃) → -E_2(α)` から `∀ᶠ n, -(1/n) log P₂^n(⋃) ≥ E_2(α) - δ`
  - `Filter.Tendsto.eventually_ge` (Mathlib) で δ-loose 化

- [ ] **C-7 `hoeffding_tradeoff_achievability` 結論**:
  - `s_n := (E_n^* を Finset (Fin n → α) に lift)` (`Finset.biUnion E_n^* typeClassByCount` を Finset 化)
  - C-5 (Type I) + C-6 (Type II) で `s_n` が `∃ s, ...` の証拠

### 工数感

~80-120 行 (C-2 ~50 + C-3 ~20 + C-4 ~30 + C-5 ~30 + C-6 ~10 + C-7 ~10)。proof-log `yes`。

### 失敗時 fallback

- **C-3 Decidable 性 + `E_n^*` の Finset 化が肥大** (`hoeffdingConstraintSet` membership の Decidable が
  classical だと Sanov LDP の `E : ∀ n, Finset (TypeCountIndex α n)` 形に乗らない、
  `noncomputable` だらけになる):
  - `Finset.range (Fintype.card α + 1) |>.image roundedTypeIndex` 系の自前 Finset 化で回避 (~20 行)
  - 最悪 **L-HP1 (Type I 制御で自作 plumbing 30 行超過)** 発動
- **C-5 Type I 制御で自前 AEP 版が 50 行を超える**: L-HP2 発動 → Phase D で先に converse 形を decide、
  achievability を `stein_achievability` (Stein.lean:488) Qstar 流用版に縮退

---

## Phase D — Converse `limsup ≤ E_2(α)` 📋

### スコープ

任意の test (`s : Finset (Fin n → α)` with Type I `≤ alpha`) に対し
**`-((1:ℝ)/n) log (Type II) ≤ E_2(α) + δ`** を `∀ᶠ n` で示し、limsup 形に集約。

### Done 条件

- `hoeffding_tradeoff_converse` (0 sorry):

  ```lean
  theorem hoeffding_tradeoff_converse
      (P₁ P₂ : α → ℝ) (hP₁_pos hP₂_pos hP₁_sum hP₂_sum)
      (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂)
      {δ : ℝ} (hδ : 0 < δ) :
      ∀ᶠ n : ℕ in atTop, ∀ (s : Finset (Fin n → α)),
        (1 - ∑ x ∈ s, ∏ i, P₁ (x i)) ≤ alpha →
        -((1 : ℝ) / n) * Real.log (∑ x ∈ s, ∏ i, P₂ (x i))
          ≤ hoeffdingE2 P₁ P₂ alpha + δ
  ```

### ステップ

- [ ] **D-1 Qstar 取り出し + full-support** (Phase C と同様):
  - `obtain ⟨Qstar, hQs_mem, hQs_min⟩ := hoeffdingE2_attained ...`
  - `have hQs_pos := hoeffdingE2_minimizer_full_support ...`

- [ ] **D-2 Stein typicality template Qstar 流用**:
  - **`stein_strong_lemma`** (`StrongStein.lean:498`) を `P := pmfToMeasure Qstar`, `Q := pmfToMeasure P₂` で起動
  - 結論: `Tendsto (fun n => -((1:ℝ)/n) * Real.log (steinOptimalBeta Qstar_meas P₂_meas n ε)) atTop (𝓝 (klDiv Qstar_meas P₂_meas).toReal)`
  - **`1 - ε` 因子を回避するため strong Stein (strict Tendsto 形) を使う** (在庫 §危険 4)

- [ ] **D-3 任意 test → typicality set 経由の下界**:
  - 任意 `s : Finset (Fin n → α)` with `(1 - ∑_s P₁^n) ≤ alpha`、即ち `P₁^n s ≥ 1 - alpha`
  - Csiszar Pythagoras (`csiszar_pythagoras_inequality`) で `K` 内の任意 Q に対し
    `klDivPmf Q P₂ ≥ klDivPmf Q Qstar + klDivPmf Qstar P₂ ≥ klDivPmf Qstar P₂ = E_2(α)`
  - typicality set `steinTypicalSet Qstar_meas P₂_meas n ε` 上で `Q^n s` が支配される

- [ ] **D-4 `Tendsto` 引き出し**:
  - `stein_strong_lemma` 結論を `.eventually_le` で `∀ᶠ n, -(1/n) log (Type II of any test with Type I ≤ alpha) ≤ E_2(α) + δ` 形に下ろす

### 工数感

~60-100 行 (D-1 ~10 + D-2 ~20 + D-3 ~40 + D-4 ~10)。proof-log `yes`。

### 失敗時 fallback

- **D-2 で `stein_strong_lemma` の Qstar 流用 + pmf↔Measure bridge が 30 行超え**: L-HP3 発動 → Stein 標準形 (`stein_lemma`, Stein.lean:1390) を流用、`1 - ε` 因子は ε-外側ループで吸収 (~20 行追加)
- **D-3 Csiszar Pythagoras の `K` 内の Q への適用で `Q ∈ K` の判定が綺麗に書けない**: `K` の Decidable 性を
  classical で済ます (Phase C-3 と同様)、または **Stein typicality set 上の Q の分布が直接 K 内の type に
  対応する**ことを示して回避

---

## Phase E — 主定理 wrapper `hoeffding_tradeoff` 📋

### スコープ

Phase C (achievability, `liminf ≥ E_2(α)`) + Phase D (converse, `limsup ≤ E_2(α)`) を
**sandwich Tendsto** で結合し、`hoeffding_tradeoff` を publish。

### Done 条件

- `hoeffding_tradeoff` Tendsto 形 (0 sorry):

  ```lean
  theorem hoeffding_tradeoff
      (P₁ P₂ : α → ℝ) (hP₁_pos hP₂_pos hP₁_sum hP₂_sum)
      {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂) :
      Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
        atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha))
  ```

- (任意) `hoeffding_tradeoff_dotEq` corollary (`steinTypeII_at_level_pmf ≐ exp(-n · E_2(α))`)

### ステップ

- [ ] **E-1 sandwich**:
  - `tendsto_of_le_liminf_of_limsup_le`:
    - `liminf ≥ E_2(α)`: Phase C から (`∀ᶠ n, ∃ s, ...` を `liminf` 形に集約)
    - `limsup ≤ E_2(α)`: Phase D から (`∀ᶠ n, ∀ s, ...` を `limsup` 形に集約)
  - `IsCoboundedUnder` 仮定の解消: `IsBoundedUnder.isCoboundedUnder_ge` (兄弟 plan で Chernoff.lean:1018 で実績あり)

- [ ] **E-2 `DotEq` corollary** (任意):
  - `dotEq_iff_tendsto_log_div` (Asymptotic.lean:116) 経由
  - `steinTypeII_at_level_pmf P₁ P₂ n alpha ≐ exp(-n · hoeffdingE2 P₁ P₂ alpha)` 形

### 工数感

~20-30 行 (sandwich ~15 + cobounded plumbing ~10 + DotEq corollary ~5)。proof-log `no` (skeleton 揃ったあとの整地)。

### 失敗時 fallback

- **E-1 で `liminf`/`limsup` への集約が想定外に肥大** (Phase C/D の `∀ᶠ n, ∃/∀ s` 形を `liminf`/`limsup` 形に変換する step が 30 行を超える):
  - 中間補題 `steinTypeII_at_level_pmf_eventually_bounded` を切り出し、`Real.log_le_log` + `Filter.Eventually.le_liminf` 系の plumbing を集約

---

## Phase V — verify + InformationTheory.lean 編入 📋

### スコープ

`InformationTheory/Shannon/HoeffdingTradeoff.lean` を 0 sorry で確定し、library root に編入。

### Done 条件

- `lake env lean InformationTheory/Shannon/HoeffdingTradeoff.lean` silent (0 errors, 0 sorry, minimal warnings)
- `InformationTheory.lean` の Shannon section に `import InformationTheory.Shannon.HoeffdingTradeoff` 追記 (順序は `InformationTheory.Shannon.Chernoff` の後ろ、依存上)
- `lake env lean InformationTheory.lean` silent

### ステップ (オーケストレータ側、本 plan の実装 agent は触らない)

- [ ] **V-1**: `lake env lean InformationTheory/Shannon/HoeffdingTradeoff.lean` で 0 sorry 確認
- [ ] **V-2**: `InformationTheory.lean` に import 行追記 (位置: `import InformationTheory.Shannon.Chernoff` の直後)
- [ ] **V-3**: `lake env lean InformationTheory.lean` で全体 silent 確認
- [ ] **V-4**: 本 plan の進捗ブロックを `✅` に更新、判断ログに publish 完了の append

### 工数感

~5 分 (オーケストレータ側で実施)。

---

## 撤退ライン

### Scope 縮小ライン (継承 + 新規)

- **L-S1** (兄弟 plan からの継続): T1-D Tendsto 形を T1-B converse と共有 plumbing で defer、本 plan で
  単独 publish する **— 既に発動済**、本 plan が L-S1 状態での publish 先 (継続)

- **L-H4** (本 plan 固有, 在庫 §撤退ラインより): **本 plan で「Tendsto 形」が組めない場合、`hoeffdingE2`
  の variational expression のみ publish**
  - 発動条件: Phase C or Phase D が 1.5 セッション (~150 行) を超えても完成しない
  - 縮退案: `hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂` を **definition + uniqueness** (兄弟 plan で
    既に publish 済の `hoeffdingE2_attained` / `hoeffdingE2_unique`) で書き切り、`Tendsto` 形は次々セッションに
    defer。本 plan は `hoeffding-tradeoff-variational-plan.md` として close
  - 縮退後の publish 単位: Phase A + Phase B のみ完遂 (~100 行)、Phase C-E は別 plan へ

### 自作 plumbing 肥大ライン (新規, 在庫 §撤退ラインを本 plan に正式 import)

- **L-H1**: **pmf↔Measure bridge plumbing が 50 行を超えた場合**
  - 発動条件: Phase A の `pmfToMeasure` family が想定 ~30 行を超えて肥大
  - 縮退案: pmf 形 `steinTypeII_at_level_pmf` を **直接** 自前 typicality set + 自前 Sanov LDP 経路で書く
    (Sanov LDP を pmf 経路に乗せる helper を別 plan で書く)。判断 #1 で確定した「候補 (a)」を「候補 (b)」または
    「候補 (c)」にピボット

- **L-H2**: **Csiszar Pythagoras 経由の minimizer 仮定立証 (Phase C-2) が 80 行を超えた場合**
  - 縮退案: `csiszar_pythagoras_inequality` を直接呼ばず、Qstar minimizer 性を
    `klDivPmf_strictConvexOn_left` + `csiszar_projection_unique` で local に再構成
    (Pythagoras 不等式の弱形だけで通せる場合がある)

- **L-H3**: **Stein converse template (`steinTypicalSet_Q_prob_le`) の Qstar 流用で `1 - ε` 因子の bias が
  `hoeffdingE2` への上界に伝播する場合**
  - 縮退案: Strong Stein (`StrongStein.lean:498` `stein_strong_lemma`, strict Tendsto 形) を直接流用
    (本 plan の Phase D は既にこれを採用予定だが、`stein_strong_lemma` の流用が想定より複雑な場合の保険)、
    または `1 - ε` 因子を `ε → 0` 極限で吸収する追加 ε-外側ループを実装

### 自作 plumbing 肥大 (Phase 固有, 新規)

- **L-HP1**: **Phase C-5 (Type I 制御) の自前 AEP plumbing が 50 行を超えた場合**
  - 縮退案: Type I 制御を Sanov LDP for `P := P₁, Q := P₁` 自己呼び出し (degenerate case) で書き直す、
    Mathlib `sanov_ldp_equality` の `h_minimizer` 仮定が trivial (`klDivPmf P₁ P₁ = 0`) で通る

- **L-HP2**: **Phase C-3 (acceptance region E_n^* の Finset 化 + Decidable 性) が 40 行を超えた場合**
  - 縮退案: `hoeffdingConstraintSet` membership を **`Classical.dec`** で全部 noncomputable にして
    Sanov LDP の `E : ∀ n, Finset` 形に `Finset.univ.filter (Classical.dec ...)` で乗せる

- **L-HP3**: **Phase D-2 (Stein typicality template Qstar 流用) の pmf↔Measure bridge plumbing が 30 行を超えた場合**
  - 縮退案: `stein_strong_lemma` の代わりに `stein_lemma` 標準形を流用、`1 - ε` 因子は ε-外側ループで吸収

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **Qstar full-support 性 (Phase B 核補題)** が反転論証で詰まる (在庫 §危険 1) | **高** | **致命** (Phase C/D/E 全て破綻) | B-2 で **midpoint + ε perturbation** の反転論証を 30-50 行で書く。最悪 `csiszar_projection_exists` の証明本体に full-support 保証が暗黙に含まれているか確認 (Chernoff.lean:310 の証明再読) |
| **pmf↔Measure bridge plumbing が 50 行超** (在庫 §危険 3) | 中 | 中 (Phase A で +30-50 行、Phase C/D に波及) | Phase 0' の判断 #1 で bridge 方針を確定 (推奨 候補 (a))。Phase A で L-H1 発動を早期検知 |
| **Stein converse template の `1 - ε` 因子が `hoeffdingE2` 上界に伝播** (在庫 §危険 4) | 中 | 中 (Phase D で +50 行 or limsup not tight) | Phase D-2 で **strong Stein (`stein_strong_lemma`, strict Tendsto 形) を直接流用** することで `1 - ε` 因子を回避する設計を確定 |
| **Sanov LDP per-Qstar の `E_n^*` 構成 + minimizer 仮定の per-`c` 整理が plumbing 30-50 行を超える** (在庫 §危険 2) | 中-高 | 中 (Phase C で +30-50 行) | Phase C-2 (`hoeffding_sanov_minimizer`) と Phase C-3 (`E_n^*` 構築) を 2 つの独立補題に切り分け、Decidable 性は `Classical.dec` で済ます (L-HP2 で保険) |
| **Type I 制御 (Phase C-5) の自前 AEP 版が想定より長い** (在庫 §危険 5) | 中 | 中 (+30 行 or Sanov LDP for `P := P₁, Q := P₁` 自己呼び出し) | Phase C 着手時に判定、L-HP1 で保険 |
| **Phase D の任意 test → typicality set 経由の下界 (D-3) で `Q ∈ K` の判定が classical/noncomputable で詰まる** | 低-中 | 中 (+20-30 行) | Stein typicality set 上の type の分布が **直接 K 内の type に対応する**ことを示して回避、または Classical.dec で済ます |
| **規模が在庫見積上限 (410 行) を超える** | 中 | 中 (1 セッションで完走できない) | Phase 単位で撤退ライン L-H4 (variational 縮退) 発動可能に設計済。Phase B 完了 (Qstar full-support + minimizer 整理) でも publish 価値あり (途中 close でも variational form は持つ) |
| **`hoeffdingE2_minimizer_full_support` で `h_alpha_lt : alpha < klDivPmf P₁ P₂` 仮定が edge case で外れる** | 低 | 低 (statement 修正で吸収) | edge case (`alpha = klDivPmf P₁ P₂` で Qstar = P₂) を別 statement で書き分け、本 plan の主 statement は `alpha < klDivPmf P₁ P₂` の strict 形で進める |

---

## オーケストレータ注記

- **実装 agent は `InformationTheory.lean` ルートを編集しない**: Phase V で本 plan が完成したあと、オーケストレータが
  まとめて `import InformationTheory.Shannon.HoeffdingTradeoff` を追加し `lake env lean InformationTheory.lean` で
  全体 silent を確認する
- **実装 agent はコミットしない**: 各 Phase 完了 (例えば Phase A の `steinTypeII_at_level_pmf` 定義 + 基本性質
  publish) のたびに、本 plan の進捗ブロックを `🚧` → `✅` に更新するだけ、コミットはオーケストレータが
  Phase A〜E 完遂後にまとめて行う
- **撤退ライン発動時は判断ログに記録 + 達成範囲で publish クローズ可**: L-H4 発動の場合、Phase B 完了 (Qstar
  full-support + `hoeffdingConstraintSet_convex` の公開 lemma 化) だけで一旦 close、`hoeffding-tradeoff-variational-plan.md`
  として残スコープを切り出す
- **実装 agent は Phase 0' (判断 #1) を Phase A 着手前に必ず実施**: pmf↔Measure bridge 方針を確定しないと
  Phase A の skeleton signature が定まらない

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-19) Phase 0' judgement #1: pmf↔Measure bridge は候補 (a) で確定** —
   `PMF.ofFintype` + `PMF.toMeasure` 経由で `pmfToMeasure : (α → ℝ) → ... → Measure α` を 1 本化。
   実装結果: ~30 行 / 4 補題 (`pmfToMeasure`, `pmfToMeasure_isProbabilityMeasure`,
   `pmfToMeasure_apply_singleton`, `pmfToMeasure_real_singleton`, `pmfToMeasure_pos`)。
   L-H1 (50 行超過) には到達せず, 想定通りの規模感。

2. **(2026-05-19) Phase B-2 `hoeffdingE2_minimizer_full_support` で L-H4 適用** —
   反転論証 `Qstar' := (1/2) Qstar + (1/2) P₁` (P₁ ∈ K + 凸結合) で
   `klDivPmf Qmid P₂ < (1/2) klDivPmf Qstar P₂ + (1/2) klDivPmf P₁ P₂` (strict convexity) と
   `klDivPmf Qmid P₂ ≥ klDivPmf Qstar P₂` (Qstar minimum) を組み合わせると, 結論は
   `klDivPmf Qstar P₂ < klDivPmf P₁ P₂` であり, これは **矛盾ではない** (Qstar が P₁ を改善する
   ことを言っているだけ). midpoint perturbation だけでは Qstar full-support に到達できない。
   正しい argument は **log-singularity に基づく gradient 引数** (Qstar の 0-atom 方向への
   摂動の方向微分が `-∞` ⇒ Qstar の minimum 性に矛盾) で, ~30-50 行の HasDerivAt + Real.log
   singularity 計算が必要。本セッション scope を超えるため,
   **`hoeffdingE2_minimizer_full_support` を publish せず**, 代わりに downstream lemma
   (`hoeffding_minimizer_ge`) を **`hQs_pos` 引数取り hypothesis 形** で publish。

3. **(2026-05-19) Phase C/D を L-H4 で defer** — 兄弟 plan L-S1 が本 plan に正式 import
   される際の想定通り, Phase C (achievability, Sanov LDP per-Qstar + Type I 自前 AEP) +
   Phase D (converse, Stein typicality 流用 + Pythagoras) は合計 200-300 行の追加スコープ。
   本セッション (~1 セッション目) では Phase A + Phase B partial + Phase E hypothesis 形で
   止め, full sandwich Tendsto は **次々セッション** (`hoeffding-tradeoff-sandwich-plan.md`
   として残スコープを切り出し)。
   現セッションの publish 範囲:
   - `pmfToMeasure` family (Sanov LDP per-Qstar の前提条件 plumbing)
   - `steinTypeII_at_level_pmf` 定義 + 基本性質 (nonneg, ≤ 1)
   - `hoeffdingConstraintSet_convex` (Chernoff.lean local helper の公開化)
   - `hoeffding_minimizer_ge` (Csiszar Pythagoras の Qstar minimizer 整理)
   - `hoeffding_tradeoff_with_hypothesis` (sandwich Tendsto, hypothesis 形)

   合計 316 行, 0 sorry。

4. **(2026-05-20) Phase C/D の残スコープを `hoeffding-tradeoff-sandwich-plan.md` に正式切り出し** —
   判断 #3 で予告した残スコープ (achievability `h_liminf` + converse `h_limsup` の 2 変分仮定 discharge) を
   サブ計画 [`hoeffding-tradeoff-sandwich-plan.md`](hoeffding-tradeoff-sandwich-plan.md) に起草。
   設計の核は **abstract L-H4 (`hoeffdingE2_minimizer_full_support`) を `alpha` の 3-case 分割
   (α=0 / 0<α≤klDivPmf P₂ P₁ / klDivPmf P₂ P₁≤α) で構成的に回避** する点 (各 case の constructive
   minimizer 補題は既に 0-sorry 完成済)。残リスクは Phase 3 の Type-I AEP のみに局所化。

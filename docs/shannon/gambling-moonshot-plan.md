# Gambling (Kelly doubling rate) ムーンショット計画 🌙

Cover–Thomas *Elements of Information Theory* Ch.6, **Theorem 6.1.2** — 比例賭け
(proportional / Kelly betting) の doubling-rate 最適性を **proof-done** (0 sorry / 0 @residual /
sorryAx-free / 独立 `@audit:ok`) まで形式化する。Ch.6 (Gambling) は `docs/textbook-roadmap.md`
の `## scope-out` ブロックで全体 `✖ scope-out` だが、本計画はその **tractable な解析核** (doubling-rate 最適性)
のみを genuine closure する (operational な株式市場 / horse-race operational 部は scope-out 継続)。

コードは新規 file `InformationTheory/Shannon/Gambling/Basic.lean`、namespace
`InformationTheory.Shannon.Gambling`。親 moonshot 無し (roadmap の 1 row を genuine 化する
自立計画)。

## 進捗

- [ ] Phase 0 — M0 API 在庫 (5 補題の verbatim 署名再確認) 📋
- [ ] Phase 1 — skeleton (def + 5 定理 `:= by sorry`、root import 登録) 📋
- [ ] Phase 2 — 閉形式 `doublingRate_proportional_eq` + 保存則系 #5 📋
- [ ] Phase 3 — headline `doublingRate_le_proportional` (CT 6.1.2) 📋
- [ ] Phase 4 — 等号条件 `doublingRate_eq_proportional_iff` 📋
- [ ] Phase 5 — 配線 (README / roadmap / 独立監査) 📋

## ゴール / Approach

**ゴール** (`α : Type*` `[Fintype α]`、`p b o : α → ℝ`):

```lean
noncomputable def doublingRate (b o p : α → ℝ) : ℝ := ∑ x, p x * Real.log (b x * o x)

-- #2 閉形式:  W* = ∑ p·log o − H(p)
theorem doublingRate_proportional_eq (p o : α → ℝ) (hp : p ∈ stdSimplex ℝ α)
    (ho : ∀ x, 0 < o x) :
    doublingRate p o p = (∑ x, p x * Real.log (o x)) - ∑ x, Real.negMulLog (p x)

-- #3 headline (CT Thm 6.1.2): 比例賭け b=p が最適
theorem doublingRate_le_proportional (p b o : α → ℝ)
    (hp : p ∈ stdSimplex ℝ α) (hb : b ∈ stdSimplex ℝ α)
    (hb_pos : ∀ x, 0 < b x) (ho : ∀ x, 0 < o x) :
    doublingRate b o p ≤ doublingRate p o p

-- #4 等号条件
theorem doublingRate_eq_proportional_iff (p b o : α → ℝ)
    (hp : p ∈ stdSimplex ℝ α) (hb : b ∈ stdSimplex ℝ α)
    (hb_pos : ∀ x, 0 < b x) (ho : ∀ x, 0 < o x) :
    doublingRate b o p = doublingRate p o p ↔ b = p

-- #5 保存則系: W* + H(p) = ∑ p·log o
theorem doublingRate_proportional_add_entropy (p o : α → ℝ)
    (hp : p ∈ stdSimplex ℝ α) (ho : ∀ x, 0 < o x) :
    doublingRate p o p + ∑ x, Real.negMulLog (p x) = ∑ x, p x * Real.log (o x)
```

**Approach** — 既存 pmf-level KL (`klDivPmf`) への還元、Ch.12 MaxEntropy
`entropy_le_gibbs_of_constraints` のミラー。核となる恒等式:

```
W* − W(b) = ∑ p x (log(p x·o x) − log(b x·o x)) = ∑ p x (log p x − log b x) = klDivPmf p b ≥ 0
```

- 各項の log 分解 `log(a·o) = log a + log o` は `o x > 0`・`b x > 0` の下で `Real.log_mul` で firing。
  `p x = 0` の項は両辺 `0` で一致する (`Real.log 0 = 0`、negMulLog 0 = 0)。
- `W* − W(b) = klDivPmf p b` の同定は `klDivPmf_eq_log_diff_sum_of_Q_pos` (log-diff 形、P=p Q=b) を **逆向きに** 使う。
- 非負性は `klDivPmf_nonneg` (→ #3)、等号 `klDivPmf p b = 0 ↔ p = b` は `klDivPmf_eq_zero_iff_pmf` (→ #4)。
- 閉形式 #2 / 保存則 #5 は per-term log 分解の rearrange のみ (KL 不要)。

**引数の向きが load-bearing**: 全て `klDivPmf p b` (第1=真の分布 p、第2=賭け b)。
`klDivPmf_eq_log_diff_sum_of_Q_pos` / `_eq_zero_iff_pmf` は **第2引数 (Q=b) の正値性** を要求する。
`klDivPmf b p` と書くと `p > 0` (未仮定) が要り詰まる。実装は必ず `p b` の順で呼ぶこと。

**壁は無い**: 5 補題全て既存 sorryAx-free asset の再利用 + 初等 log 代数。proof-done 到達可能。
既存共有補題の **署名変更は一切しない** (consume のみ) ため ripple 無し (`dep_consumers.sh` 不要)。

## M0 在庫 (verbatim 署名 — 実装前に Phase 0 で再 Read 確認)

いずれも `variable {α : Type*} [Fintype α]` 文脈。`stdSimplex ℝ α` は `Mathlib` (要素 `.1 : ∀ a, 0 ≤ P a`、`.2 : ∑ a, P a = 1`)。

1. `InformationTheory/Shannon/CsiszarProjection.lean:61`
   `noncomputable def klDivPmf (P Q : α → ℝ) : ℝ := ∑ a : α, Q a * klFun (P a / Q a)`
2. `CsiszarProjection.lean:67`
   `lemma klDivPmf_nonneg (P Q : α → ℝ) (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a) : 0 ≤ klDivPmf P Q`
   — ⚠ **署名注意**: 前提は **pmf (stdSimplex) membership でなく pointwise 非負** `∀ a, 0 ≤ P a`。
   `p ∈ stdSimplex` からは `hp.1` を、`b > 0` からは `fun a => (hb_pos a).le` を渡す。
3. `InformationTheory/Shannon/MaxEntropy/Constrained.lean:287` (`omit [DecidableEq α]`)
   `lemma klDivPmf_eq_zero_iff_pmf {P Q : α → ℝ} (hP : P ∈ stdSimplex ℝ α) (_hQ : Q ∈ stdSimplex ℝ α) (hQ_pos : ∀ a, 0 < Q a) : klDivPmf P Q = 0 ↔ P = Q`
   — `_hQ` は unused だが **位置引数として必須** (= b∈stdSimplex を渡す)。
4. `InformationTheory/Shannon/Hoeffding/TradeoffExp.lean:97` (`omit [DecidableEq α]`)
   `lemma klDivPmf_eq_log_diff_sum_of_Q_pos {P Q : α → ℝ} (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1) (hQ_sum : ∑ a, Q a = 1) (hQ_pos : ∀ a, 0 < Q a) : klDivPmf P Q = ∑ a : α, P a * (Real.log (P a) - Real.log (Q a))`
5. `InformationTheory/Shannon/Chernoff/Basic.lean:225` (namespace `InformationTheory.Shannon.Chernoff`, `omit [DecidableEq α]`)
   `lemma klDivPmf_self_eq_zero (P : α → ℝ) (hP_pos : ∀ a, 0 < P a) : klDivPmf P P = 0`
   — #4 の (←) 方向で任意 (`_eq_zero_iff_pmf` の (←) が内部で使う)。直接呼ばずとも良い。

ミラー元 (route 参照): `Constrained.lean:250` `entropy_le_gibbs_of_constraints`
(= `klDivPmf_nonneg` + `_self_eq_zero` + 恒等式 + `linarith` の組立て型)。

Mathlib 側 (transitive 供給、明示 import 不要): `Real.log_mul` / `Real.negMulLog`
(= `-x·log x`、`negMulLog 0 = 0`) / `Finset.sum` / `stdSimplex`。

## Phase 0 — M0 API 在庫 📋  proof-log: no

- [ ] 上記 5 補題の cited line を Read し、`[…]` typeclass 括弧含め署名を verbatim 確認
      (特に #2 の pointwise 非負前提 + #3 の `_hQ` 位置引数 + `Real.negMulLog 0 = 0`)
- [ ] `Real.log_mul` (両因子 `≠ 0` 要求) の署名確認 → `p x = 0` 分岐を回避せず per-term で場合分けする方針を固定
- 撤退ライン: 在庫 Phase につき sorry 対象なし。

## Phase 1 — skeleton 📋  proof-log: no

- [ ] file 作成: namespace `InformationTheory.Shannon.Gambling`、import は §配線に列挙の specific module のみ
- [ ] `doublingRate` def + 5 定理を `:= by sorry` で state、LSP で型検査通過を確認 (sorry warning のみ)
- [ ] `InformationTheory.lean` root に import 行を追記
- 撤退ライン: skeleton 段階では各 `sorry` に `@residual(plan:gambling-moonshot-plan)` を付す。

## Phase 2 — 閉形式 #2 + 保存則 #5 📋  proof-log: no

- [ ] per-term 補題: `p x = 0` / `0 < p x` の場合分けで `p x * log(p x·o x) = p x·log o x − negMulLog(p x)` を証明
      (`0 < p x` 側で `Real.log_mul (p x ≠ 0) (o x ≠ 0)`、`negMulLog(p x) = -p x·log p x`)
- [ ] `doublingRate_proportional_eq` = per-term を `Finset.sum` に持ち上げ
- [ ] `doublingRate_proportional_add_entropy` (#5) = #2 の `linarith`/`ring` rearrange
- 撤退ライン: log 分解が難所化したら該当定理を `sorry` + `@residual(plan:gambling-moonshot-plan)`。
  **禁止**: 恒等式を `*Hypothesis` predicate に束ねる撤退 (honesty defect)。

## Phase 3 — headline #3 (CT Thm 6.1.2) 📋  proof-log: **yes**

- [ ] per-term `o` 分解補題: `o x > 0`・`b x > 0` の下で
      `p x * (log(p x·o x) − log(b x·o x)) = p x * (log p x − log b x)` (`p x = 0` は両辺 0)
- [ ] gap = `∑ p x (log p x − log b x)` を `klDivPmf_eq_log_diff_sum_of_Q_pos` (P=p, Q=b) で **逆向き** に `klDivPmf p b` へ
- [ ] `klDivPmf_nonneg p b hp.1 (fun a => (hb_pos a).le)` で `0 ≤ klDivPmf p b` → `doublingRate b o p ≤ doublingRate p o p`
- proof-log: `docs/proof-log-gambling-headline.md` に per-term o-split の場合分け + 引数向き (p b) を記録
- 撤退ライン: `sorry` + `@residual(plan:gambling-moonshot-plan)`。hypothesis 束ね禁止。

## Phase 4 — 等号条件 #4 📋  proof-log: no

- [ ] gap = `klDivPmf p b` の同定を Phase 3 と共有し、`klDivPmf_eq_zero_iff_pmf hp hb hb_pos : klDivPmf p b = 0 ↔ p = b`
- [ ] `doublingRate b o p = doublingRate p o p ↔ klDivPmf p b = 0 ↔ p = b`、最後に `eq_comm` で `b = p`
- 撤退ライン: `sorry` + `@residual(plan:gambling-moonshot-plan)`。

## Phase 5 — 配線 + 完成監査 📋  proof-log: no

- [ ] README: `docs/readme-theorems.txt` の Ch.6 節に `doublingRate_le_proportional` を追記 →
      `deno run -A scripts/gen_readme_table.ts --write` で再生成 (markers 内は手編集しない)
- [ ] roadmap `docs/textbook-roadmap.md`: Ch.6 は現状 `## scope-out` ブロック (l.13
      `Ch.6 Gambling / Ch.14 … / Ch.16 …`) にグルーピングされ、章対応表 (`## 章対応進捗`) も `✖`。
      MAC/BC/EPI の「もはや scope-out ではない」注記の書式に倣い、doubling-rate 最適性は genuine
      closure 済 / 残る operational (株式市場 / horse-race operational) は scope-out 継続、と注記追加
- [ ] `docs/shannon/shannon-facts.md` に headline の再検証コマンド (`#print axioms doublingRate_le_proportional`) を 1 行追記
- [ ] proof-done 到達時: 独立 `honesty-auditor` を dispatch し headline に `@audit:ok`
      (sorry 導入が無くとも本計画ゴールが独立 `@audit:ok` を要求するため)

## 正直性メモ (precondition の性質)

全 precondition は **regularity precondition** であり load-bearing hypothesis bundling ではない:

- `p ∈ stdSimplex ℝ α` — 真の pmf (定義域制約)
- `b ∈ stdSimplex ℝ α` + `∀ x, 0 < b x` — full-support の賭け
- `∀ x, 0 < o x` — 正のオッズ

**`b > 0` は genuine な correctness precondition** ("生きている馬に 0 を賭けるな")、bundling でない。
Lean は `Real.log 0 = 0` を採るため、**この前提が無いと #3 の不等式は FALSE**:
反例 `|α|=2, p=(1/2,1/2), o=(2,2), b=(1,0)` で
`W* = ∑ (1/2)·log 1 = 0` に対し `W(b) = (1/2)log 2 + (1/2)·log 0 = (1/2)log 2 > 0`、
すなわち `W(b) ≤ W*` が破れる (真の doubling rate なら `log 0 = −∞` で ruin だが Lean は 0 に潰す)。
これは仮説束ねの defect ではなく **定義規約由来の必須前提** として記録する。

## 判断ログ

(現時点 active entry 無し。方針変更 / 撤退 / 当初仮定の修正が生じたら追記。決着済は削除。)

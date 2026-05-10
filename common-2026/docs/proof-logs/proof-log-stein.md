# Proof log — Stein の補題 (Phase A〜B 完了)

> **Parent plan**: [`docs/shannon/stein-moonshot-plan.md`](../shannon/stein-moonshot-plan.md)
> **Inventory**: [`docs/shannon/stein-mathlib-inventory.md`](../shannon/stein-mathlib-inventory.md)
> **File**: [`Common2026/Shannon/Stein.lean`](../../Common2026/Shannon/Stein.lean) (625 行)
> **Status**: Phase A ✅ / Phase B ✅ (= **Stein achievability publish ライン到達**)。Phase C/D は別 plan に切り出し
> **Verification**: `lake env lean Common2026/Shannon/Stein.lean` silent (warning 0 / error 0 / sorry 0) / `lake build` 全体緑通過

## 質的観察

### 1. AEP plumbing の 2 分布化は **計画通り** 70〜80% 再利用、新規構築は B.3 のみが実質コスト

計画段階の見立て「AEP 13 補題のうち 12 が 1〜2 行の 2 分布化で済む、新規構築は 2〜3 本のみ」は **ほぼそのまま当たった**。実際の作業内訳:

- **1〜2 行の 2 分布化** (AEP の構造を `pmfLog` → `llrPmf` rename だけで再利用): `measurable_llrPmf`, `logLikelihoodRatio`, `measurable_logLikelihoodRatio`, `integrable_logLikelihoodRatio`, `identDistrib_logLikelihoodRatio`, `indepFun_logLikelihoodRatio`, `stein_strong_law`, `stein_inProbability`, `measurableSet_steinTypicalSet` — 計 9 補題、合計 80 行程度
- **構造ほぼ AEP 同型 + 期待値の identification を 2 分布版に置換** (`integral_logLikelihood_zero` → `integral_logLikelihoodRatio_under_P`): 50 行
- **構造 AEP 同型 + 確率収束対象先を変更**: `steinTypicalSet_P_prob_tendsto_one` 50 行
- **実質新規** (Q 測度上の per-point bound + sum 評価): `steinTypicalSet_Q_prob_le` 130 行
- **組み合わせ** (B.4 `stein_achievability`, statement 設計 + 細部の log monotonicity): 110 行

教訓: AEP のような確率漸近系 plumbing を整備しておくと、**派生定理 (Stein, Sanov, Chernoff) の 70〜80% は構造再利用** で実装できる。Mathlib 不在の補題 (likelihood ratio 系) を一度自前で組むコストは大きいが、それを最初に支払えば後続の派生は **薄い加算**で済む。

### 2. **`klDiv_pi_eq_n_smul` (Pi 化 chain rule) は Phase B には不要**だった

計画では Phase A.7 として `klDiv (Π P) (Π Q) = n · klDiv P Q` の Pi 化 chain rule を「Phase A の山場 1」として 40〜80 行見積で予定していた。実装着手後、**Phase B の Q 測度上界 (B.3) を point-wise で書く方針** にすると Pi 化 chain rule が不要になった:

- B.3 の証明では `Measure.pi_singleton` (`Measure.pi μ {f} = ∏ i, μ i {f i}`) で Pi 測度を point-wise の積に下し、典型集合の定義 (`(1/n) ∑ llrPmf > klDiv - ε`) を point-wise の `exp(-llrPmf x_i) = q(x_i)/p(x_i)` で展開
- これで `Π Q{x_i} ≤ Π P{x_i} · exp(-n(klDiv-ε))` が **AEP `typicalSet_card_le` の Q 測度版** として直接得られる
- Pi 化 chain rule (= 全体の KL 値の n 倍化) は **Phase C (converse) で必要**になる予定だが、Phase B では不要

教訓: **「教科書の証明戦略」と「Mathlib API に乗りやすい証明戦略」は時に異なる**。教科書 (Cover-Thomas) は chain rule を経由する高レベル形だが、Mathlib では `Measure.pi_singleton` + point-wise の方が plumbing が薄い。**「KL chain rule の Pi 化」のような大きな補題を最初から Phase A に置く」のは early commitment**、実装着手で route が見えてから決めるべき。撤退ライン (Phase A.7 で 5〜7 日溶ける) を予防する形で計画は機能した。

### 3. `Measure.pi_singleton` (`@[simp]`) で Pi 測度の point-wise 評価は **1 行**

Mathlib `Measure.pi_singleton : Measure.pi μ {f} = ∏ i, μ i {f i}` (`Mathlib/MeasureTheory/Constructions/Pi.lean:301`、`@[simp]`) で:

```lean
((Measure.pi (fun _ : Fin n => Q)).real {x}) = ∏ i : Fin n, Q.real {x i}
```

の証明が `rw [Measure.pi_singleton, ENNReal.toReal_prod]; rfl` で **1 行**で済む。Pi 測度の point-wise 評価が「1 行で出る」のは、 inventory 起草時に把握できていなかった (loogle で「Pi 測度 + singleton」を当てる query 発想がなかった)。

教訓: **Inventory で「補題 X が無い」と判定したら、まず X を point-wise / atomic に分解して再 query する**。Pi 化 chain rule (= 全体形) は不在でも、point-wise 形 (= `{f}` 形) は完備、というパターンが Mathlib にはよくある。Stein では Pi 化 KL chain rule (不在) を point-wise の `Measure.pi_singleton` (在) で迂回できた。

### 観察 (補) — 副次的教訓

- **`omit ... in` は docstring の前に置く**。docstring と theorem 宣言の間に挟むと `unexpected token 'omit'; expected 'lemma'` で詰まる (Bridge.lean の用例で確認)
- **`simp only [..., jointRV_apply]` が `[Nonempty α]` の omit で発火しなくなる症状**。原因は未調査。`set_option linter.unusedSectionVars false in theorem` で per-theorem 抑制で回避

## 撤退判断

### Phase C/D は本セッション撤退、別 plan に切り出し

**判断根拠**:
- Phase A〜B が緑通過した時点で **Stein achievability publish ラインに到達** (= Cover-Thomas Theorem 11.8.3 の半分、「ある検定で `β_n ≤ exp(-n · klDiv P Q + n · δ)`」)
- Phase C は本質的に新規 plumbing (DPI reduction + Bernoulli KL 評価 + `klDiv_pi_eq_n_smul`) で 1〜1.5 週見積、本セッションの工数枠 (1 ターン) を超える
- 計画の撤退ライン「Phase A〜B 完了 = 撤退時の publish ライン」に従い切り出し

**残課題 (次セッション以降)**:
1. **Phase A.7** `klDiv_pi_eq_n_smul` (Pi 化 KL chain rule、Phase C の前提)
2. **Phase C.1** DPI reduction (任意検定 → Bernoulli KL)
3. **Phase C.2** Bernoulli KL の評価
4. **Phase C.3** `klDiv_pi_eq_n_smul` 適用、`-(1/n) log Q^n(s) ≤ klDiv + δ_n`
5. **Phase D** 統合形 `stein_lemma` (`Tendsto` 形 lim 結論)

工数感: Phase C 単独 1〜1.5 週、Phase D 単独 0.5 週。あわせて 1.5〜2 週で完全形 `stein_lemma` まで到達可能と見込む。

## 次セッションへの引継ぎ

`Common2026/Shannon/Stein.lean` の**末尾** (line 627 付近、`stein_achievability` の直後) に Phase C 着手の sorry-driven skeleton を追加するのが自然な続き。作業順:

1. `klDiv_pi_eq_n_smul` を Phase C の前段で実装 (`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean` の `klDiv_compProd_eq_add` + `klDiv_compProd_left` + `MeasurableEquiv.piFinSuccAbove` で induction、計画 Phase A.7 参照)
2. `stein_converse` (`stein_achievability` の dual statement) skeleton を sorry-driven で書く
3. Phase D の統合形 `stein_lemma` (両側 bound → `Tendsto`) を最後に締める

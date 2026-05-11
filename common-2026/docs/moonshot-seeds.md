# Moonshot シードカード集

> **Status (2026-05-11)**: ✅ 5 シード完了 (Seed 4: AEP は Phase A〜C 単体 publish ラインで完了 / Phase D 源符号化は別 plan、Seed 5: Stein は achievability 単体で完了 / converse は別 plan)。Loomis–Whitney → Slepian–Wolf → AEP → Stein achievability → Polymatroid を **すべて 0 sorry** で通過。次のムーンショット候補は末尾「次のシード候補」セクション参照。
>
> 起草時 (2026-05-10): Fano (測度論版) → Shannon converse (3 形) → Han 補集合形 → Han Phase D (subset average / Shearer) まで通った状態を起点に、次のムーンショット候補 5 本をシード化。
>
> ここに書いてあるのは **着手前の seed**。実装着手の判断 = 該当シードを `docs/<family>/<topic>-moonshot-plan.md` に複製 + `docs/moonshot-plan-template.md` で膨らませる。本ファイル自体はカード一覧として保ち、選定が確定したら該当カードに `→ <plan path>` のポインタを書き加える。

## 起点 (現場実装)

**初期 (Seed 起草時、2026-05-10)**:
- `Common2026/Fano/Measure.lean` — `fano_inequality_measure_theoretic` (deterministic decoder)
- `Common2026/Shannon/{MutualInfo,DPI,Bridge,CondMutualInfo,Converse}.lean` — KL 主軸 single-shot Shannon converse 3 形 + Markov chain + chain rule
- `Common2026/Shannon/{Entropy,Han,HanD,HanDAverage,HanDShearer}.lean` — 2 変数 / Fin n / Finset (Fin n) の chain rule + conditioning monotonicity + Han 補集合 + Han 1978 subset average + Shearer

**追加 (5 シード完了後、2026-05-11)**:
- `Common2026/Shannon/Pi.lean` — `entropy_measurableEquiv_comp` / `condEntropy_measurableEquiv_comp` (横断整理で切り出し)
- `Common2026/Shannon/LoomisWhitney.lean` — Seed 1 完了 (444 行、Shearer 適用で `|A|^{n-1} ≤ ∏ |π_i(A)|`)
- `Common2026/Shannon/SlepianWolf.lean` — Seed 3 完了 (511 行、3 bound + side info Fano)
- `Common2026/Shannon/AEP.lean` — Seed 4 Phase A〜C 完了 (432 行、`aep_inProbability` + `aep_ae` + typical set 3 性質)
- `Common2026/Shannon/Stein.lean` — Seed 5 Phase A〜B 完了 (626 行、Stein achievability)
- `Common2026/Shannon/Polymatroid.lean` — Seed 2 完了 (288 行、submodularity + monotonicity + empty=0)

このスタックを「異なる角度で擦る」5 本を以下に並べる。

---

## Seed 1: Loomis–Whitney 不等式 🌙 ✅ 完了 (2026-05-11)

**カテゴリ**: Shearer 組合せ応用 (情報理論外への漏出)

**Statement (組合せ形)**:
```
∀ A ⊆ Π_{i : Fin n} α_i,
  |A|^(n-1) ≤ ∏_{i : Fin n} |π_i(A)|
```
ここで `π_i` は `i` 成分を落とす射影。

**再利用**:
- `shearer_inequality` を `S i := {j | j ≠ i} : Finset (Fin n)` (各 j は `n-1` 個の S に被覆) で適用
- 一様分布の entropy と濃度の橋渡し (`entropy μ Xs = log |A|` for `μ = 一様 on A`)

**新規**:
- counting measure 上での `entropy` 評価補題 (Han の `entropy_measurableEquiv_comp` の counting 版)
- 各射影像 `π_i(A)` の濃度評価を marginal entropy に対応させる plumbing

**Why moonshot**:
- 「Shearer は情報理論外でも効く」を Lean で実演する textbook 級の応用
- Mathlib に Loomis–Whitney 不在 (要 inventory 裏取り)
- Han Phase D 完成直後の最高の payoff デモ

**工数 / リスク**: 1〜2 週間 / 200〜300 行 / **低リスク** (新規測度論ゼロ、純コンビと既存 Shearer の合成のみ)

**依存 / 後続**: 単独で立つ。後続に edge-isoperimetry / hypercube combinatorics の入口が開く。

→ `docs/shannon/loomis-whitney-moonshot-plan.md` (Phase 0/A/B/C すべて ✅) / 実装: `Common2026/Shannon/LoomisWhitney.lean` (444 行、0 sorry) / proof-log: `docs/proof-logs/proof-log-loomis-whitney.md`

---

## Seed 2: Submodularity of entropy / polymatroid axioms ✅ 完了 (2026-05-11)

**カテゴリ**: Han Phase D の構造的整理

**Statement**:
```
∀ S T : Finset (Fin n),
  jointEntropySubset μ Xs (S ∪ T) + jointEntropySubset μ Xs (S ∩ T)
    ≤ jointEntropySubset μ Xs S + jointEntropySubset μ Xs T
```
+ `S ⊆ T ⇒ jointEntropySubset μ Xs S ≤ jointEntropySubset μ Xs T` (monotonicity)
+ `jointEntropySubset μ Xs ∅ = 0`

これで entropy が **polymatroid rank function** になることを示す。

**再利用**:
- `condEntropy_subset_anti` (Han Phase D Phase A)
- `jointEntropySubset_chain_rule` で `H(X_T) - H(X_{S∩T}) = H(X_{T\S} | X_{S∩T})` の形に直す

**新規**:
- 集合論的 reshape: `S ∪ T = S ⊔ (T \ S)` の Pi 値同値 (`MeasurableEquiv` 1〜2 本)
- `jointEntropySubset_empty = 0` の補題 (`Fin 0 → α ≃ Unit` 経由)
- (オプション) `Polymatroid` という structure を導入するかどうかは判断保留

**Why moonshot**:
- 「entropy が polymatroid」は情報理論と組合せ最適化を繋ぐ根本構造 (Lovász, Fujishige)
- Mathlib に `Polymatroid` / `Submodular` (集合関数版) は不在 (要確認)
- Han の subset 機械を最終的に payoff させる定理。Han Phase D 後の自然な後始末

**工数 / リスク**: 1〜2 週間 / 300〜400 行 / **低〜中リスク** (Han Phase D の plumbing が直接効く)

**依存 / 後続**: 単独で立つ。後続に matroid 理論 / 結合構造論への入口。

→ `docs/han/polymatroid-moonshot-plan.md` (Phase A/B/C ✅、Phase D structure 化は別 plan に切り出し) / 実装: `Common2026/Shannon/Polymatroid.lean` (288 行、0 sorry) / proof-log: `docs/proof-logs/proof-log-polymatroid.md`

---

## Seed 3: Slepian–Wolf 単発 converse 🌙 ✅ 完了 (2026-05-10)

**カテゴリ**: Shannon converse の distributed 拡張

**Statement (single-shot 形)**:
```
2 つの encoder e_X : X → [M_X], e_Y : Y → [M_Y] と
joint decoder d : [M_X] × [M_Y] → X × Y が
  P{ d(e_X(X), e_Y(Y)) ≠ (X, Y) } ≤ ε
を満たすなら
  log M_X ≥ H(X | Y) - δ(ε)
  log M_Y ≥ H(Y | X) - δ(ε)
  log M_X + log M_Y ≥ H(X, Y) - δ(ε)
where δ(ε) := h(ε) + ε · log(|X × Y| - 1)  -- Fano 由来
```

**再利用**:
- `shannon_converse_single_shot` の論法 → 3 系の Fano に分解して適用
- `entropy_pair_eq_entropy_add_condEntropy` で `H(X,Y) = H(X) + H(Y|X)` の chain rule
- `mutualInfo_le_of_postprocess` (DPI) を side info の取り扱いに

**新規**:
- 「2 ソースが片方の encoded 出力 + 真値を side info に持つ」formulation の設計
- side info 入りの Fano (`condEntropy μ Xs (Yo, sideInfo) ≤ ...`) — Phase 3 Fano + side info 接続
- 3 つの bound を 1 statement にまとめる構造 (3 つを別 theorem にしてもよい)

**Why moonshot**:
- Cover-Thomas 15.4 の中核
- Shannon converse の自然な multi-source 拡張で **「単一 converse が複数 converse の合成として組めるか」**を検証する
- Mathlib 未実装。「第二の converse」として記事化価値が高い

**工数 / リスク**: 2〜3 週間 / 400〜600 行 / **中リスク** (formulation 設計に 1 ターン要、side info 入り Fano の自前 plumbing が想定外に重い可能性)

**依存 / 後続**: Seed 4 (AEP) ができれば asymptotic 化が直接続けられる。本 seed は single-shot 単独で publish 価値あり。

→ `docs/shannon/slepian-wolf-moonshot-plan.md` (Phase A/B/C ✅) / 実装: `Common2026/Shannon/SlepianWolf.lean` (511 行、0 sorry、3 bound) / proof-log: `docs/proof-logs/proof-log-slepian-wolf.md`

---

## Seed 4: AEP + 源符号化定理（漸近）🌙🌙 ✅ 部分完了 (2026-05-11)

**カテゴリ**: single-shot → `n → ∞` への跳躍

**Statement** (本命: 源符号化定理 weak converse):
```
∀ ε > 0, X : Ω → α (i.i.d. 列の base distribution),
任意の (deterministic) c_n : (Fin n → α) → Fin (M_n), d_n : Fin (M_n) → (Fin n → α) で
  P{ d_n(c_n(X^n)) ≠ X^n } → 0   ⟹   liminf_n (log (M_n : ℝ) / n) ≥ entropy μ X
```
+ 逆向きに rate > H(X) で error → 0 (typicality 構成、achievability 半分)。

**サブステップ (AEP)**:
```
∀ ε > 0,
  P{ |−(1/n) log P(X^n) − H(X)| ≥ ε } → 0  (probability AEP)
typical set T_ε^n := { x^n : |−(1/n) log P(x^n) − H(X)| < ε } に対し
  |T_ε^n| ≤ 2^{n(H(X)+ε)}
  P(X^n ∈ T_ε^n) → 1
```

**再利用**:
- Han Phase B で確立した `Fin n → α` Pi 値 RV plumbing (i.i.d. 列の codomain)
- Mathlib `MeasureTheory.LLN` (`stronglyMeasurable_lln` / 強法則) を `−log P(X)` に適用
- `shannon_converse_single_shot` を block に持ち上げ (`X^n` rate との比較)

**新規 (重い)**:
- i.i.d. 列の formal definition (`IsIID Xs μ` のような predicate、`Mathlib/Probability/IdentDistrib.lean` に既存材料あり、要 inventory)
- typical set の measurability + 積分可能性 plumbing
- `−(1/n) log P(X^n)` の log 取扱と `liminf` への乗せ替え
- block error → liminf bound の Fano 適用 (`shannon_converse_single_shot` を `M = M_n` で繰り返し呼ぶ)

**Why moonshot**:
- **Common2026 を「single-shot 限定」から「漸近情報理論」に格上げする最大の関門**
- Cover-Thomas Ch 3 (AEP) + Ch 5 (源符号化) の中核
- Mathlib の Probability / LLN 基盤を本気で擦る初テーマ → どこが薄いかの可視化

**工数 / リスク**: 4〜6 週間 / 800〜1500 行 / **高リスク**:
- LLN を `−log P(·)` に乗せる際の可測性 / 可積分性で詰まる可能性大
- `liminf` を扱う Mathlib API (`Filter.liminf`) と教科書の `lim` formulation の reconciling
- 撤退ライン: AEP 単体 (probability + typical set size + typicality probability) まで → 源符号化定理本体は将来

**依存 / 後続**: Seed 5 (Stein) の plumbing 半分を共有。Seed 4 → 5 の順序が自然。本 seed が片付けば Common2026 全体の射程が一気に広がる。

→ `docs/shannon/aep-moonshot-plan.md` (Phase A/B/C ✅ AEP 単体 publish ラインに到達 / Phase D 源符号化定理 weak converse + Phase E achievability は撤退ラインに従って次セッションへ deferred) / 実装: `Common2026/Shannon/AEP.lean` (432 行、0 sorry) / proof-log: `docs/proof-logs/proof-log-aep.md`

---

## Seed 5: Stein の補題（仮説検定の最適 error exponent） ✅ 部分完了 (2026-05-11)

**カテゴリ**: KL の operational meaning、統計的仮説検定

**Statement**:
```
2 つの分布 P, Q : Measure α (P ≪ Q),
i.i.d. サンプル X^n からの検定 A_n ⊆ α^n (A_n ∈ rejection region) で
type-I error α_n := P^n(A_n^c) ≤ ε を保証するもののうち
type-II error β_n := Q^n(A_n) を最小化すると
  -lim_n (1/n) log β_n = klDiv P Q
```

**再利用**:
- `klDiv` (Mathlib) + `klDiv_compProd_eq_add` で `klDiv P^n Q^n = n · klDiv P Q` (i.i.d. への chain rule の直接系)
- AEP 風の typicality 議論 (Seed 4 と plumbing 共有)
- `klDiv_eq_zero_iff` 等 Phase 4-α で確立した KL 性質

**新規**:
- 検定 (= 可測集合 + 確率 ε バウンド) の formalism
- likelihood ratio test の構成と漸近最適性
- `liminf` / `lim` 取り扱い (Seed 4 と共通)
- log-likelihood ratio の log 可測性

**Why moonshot**:
- **「KL が単なる divergence ではなく検定の指数として operational に意味を持つ」**ことを Lean で示す
- Cover-Thomas 11.8。情報理論と統計的仮説検定の橋渡し
- Mathlib の `klDiv` を本格応用する初の漸近 statement

**工数 / リスク**: 3〜4 週間 / 600〜900 行 / **中〜高リスク**:
- AEP 機械が Seed 4 で出来ていれば軽くなる (Seed 4 → Seed 5 の順序が自然)
- 検定 / hypothesis testing の formalism は Mathlib に薄い可能性 (要 inventory)

**依存 / 後続**: Seed 4 (AEP) を先にやると plumbing の半分が共有できる。逆は不可 (Seed 5 単独だと AEP を内側に再実装する羽目になる)。

→ `docs/shannon/stein-moonshot-plan.md` (Phase A/B ✅ Stein achievability 単体 publish ラインに到達 / Phase C upper bound + Phase D 統合形 `stein_lemma` (両側等号) は別 plan として切り出し) / 実装: `Common2026/Shannon/Stein.lean` (626 行、0 sorry) / proof-log: `docs/proof-logs/proof-log-stein.md`

---

## 依存グラフと推奨順序

```
Seed 1 (Loomis–Whitney) ──┐
                          │  独立、いつでも着手可
Seed 2 (Polymatroid)   ──┘

Seed 3 (Slepian–Wolf) ──→ (asymptotic 化は Seed 4 後)

Seed 4 (AEP + 源符号化) ──→ Seed 5 (Stein)
```

**短期 publish ライン (1〜2 週間 × 1 本)**: Seed 1 または Seed 2
**中期メイン (2〜3 週間 × 1 本)**: Seed 3
**長期本命 (4〜6 週間 + 3〜4 週間)**: Seed 4 → Seed 5 のチェーン

過去 Phase の 3 段構造 (小応用 → 中継ぎ → 跳躍) と整合させるなら **Seed 1 → Seed 3 → Seed 4 → Seed 5** の 4 連が中心ライン。Seed 2 は Seed 1 と同等の重みで side track 可。

---

## 次のシード候補 (5 シード完了後、2026-05-11)

5 シード完了で生まれた **deferred / sub-plan 候補** と **新規候補**:

### A. 直接 deferred (本セッションの撤退ラインに従って分離)

- ~~**Stein converse (Phase C/D)**: `-(1/n) log β_n ≤ klDiv P Q + δ` の upper bound + 両側統合 `Tendsto` 形 `stein_lemma`。Phase A〜B (achievability) が `Common2026/Shannon/Stein.lean` で 0 sorry で立っているのが起点。新規 plumbing は (a) 任意検定 → Bernoulli KL の DPI reduction、(b) `klDiv (P^n) (Q^n) = n · klDiv P Q` の Pi 化 chain rule (40〜80 行の induction)、(c) 統合形の `Tendsto` 構築。見積 1〜1.5 週間 / 200〜400 行 / 中リスク。~~ → ✅ 部分完了 (2026-05-11): converse 半分の concrete inequality 形 (`stein_converse_finite_n : -(1/n) * log (Q^n s) ≤ (1/(1-ε)) * (klDiv P Q + h(ε)/n)`) を `Common2026/Shannon/Stein.lean` に追加 (+497 行)。新規 plumbing 完了: (a) Pi 化 KL chain rule (`klDiv_pi_eq_n_smul`、Phase A 98 行 induction)、(b) DPI reduction (`Common2026/Shannon/DPI.lean:52` の `klDiv_map_le` を public 化、Bool 上 reduction + `mul_log_le_toReal_klDiv` で log-sum 下界、Phase B 398 行)。Phase C (`Tendsto` 形 `stein_lemma` 統合、`steinOptimalBeta` + sInf + liminf squeeze + `inf_ε` で `1/(1-ε)` 補正項を absorb) は別 plan に切り出し → plan: `docs/shannon/stein-converse-plan.md` / 実装: `Common2026/Shannon/Stein.lean` (新規 Phase A〜B converse 部) + `Common2026/Shannon/DPI.lean` (1 行 visibility)
- **Stein Tendsto 形統合 (Phase C 後段)**: `Common2026/Shannon/Stein.lean` の `stein_converse_finite_n` (concrete inequality) と achievability lower bound を合わせて `stein_lemma : Tendsto (fun n => -(1/n) * log (steinOptimalBeta P Q n ε)) atTop (𝓝 (klDiv P Q))` (または liminf 形 `liminf_n (-(1/n) * log β_n) = klDiv P Q`) を構築。新規 plumbing: (a) `steinOptimalBeta` def + sInf plumbing、(b) Filter.liminf squeeze + `inf_ε` で `1/(1-ε)` 補正項を absorb。proof 本体に新規数学なし (Filter / sInf API plumbing のみ)。見積 100〜200 行 / 低〜中リスク。起点完備 (`stein_converse_finite_n` + achievability 0 sorry)。
- **AEP Phase F 両側等号 unified source coding theorem**: `Common2026/Shannon/AEP.lean` の `source_coding_weak_converse_aep` (Phase D, liminf ≥ H) と `source_coding_achievability` (Phase E, ∃ code with rate → R for any R > H) を合わせて両側等号 `inf_{achievable codes} liminf (log M_n / n) = entropy μ X` を構築。新規 plumbing: (a) "achievable code" の predicate (`∃ M_n c_n d_n, errorProb ... → 0`)、(b) sInf-over-achievable-codes wrapper、(c) Phase D の `hM_bdd` 仮定との整合 (achievable codes は実用 rate-bounded で常に成り立つ)。proof 本体に新規数学なし。見積 50〜100 行 / 低リスク。起点完備 (Phase D + E 0 sorry)。
- ~~**AEP Phase D (源符号化定理 weak converse)**: `liminf_n (log M_n / n) ≥ entropy μ X`。AEP 単体 (`Common2026/Shannon/AEP.lean`) が 0 sorry なので起点完備。`shannon_converse_single_shot` を block per-n 適用。`Filter.liminf` API 取り扱いが残存懸念。見積 1〜1.5 週間 / 300〜500 行 / 中リスク。~~ → ✅ 完了 (2026-05-11): `Common2026/Shannon/AEP.lean` (+368 行) に Phase A (Pi 化 entropy chain rule `entropy_jointRV_eq_n_smul`、Han route で `jointEntropy_chain_rule_finRange` + `condEntropy_eq_entropy_of_indepFun` + `entropy_eq_of_identDistrib` 経由) + Phase B (Slepian-Wolf 流儀 4-step skeleton 再演、Step C DPI は assembly 上不要で省略) + Phase C (`Filter.liminf` 形 `source_coding_weak_converse_aep`) を 0 sorry で実装。**仮定 `iIndepFun` 強化** (Phase A〜C は `Pairwise IndepFun`、Phase D は mutual 必須、`iIndepFun.indepFun` で auto derive) + **仮定 `hM_bdd : ∃ R, ∀ n, log M_n / n ≤ R` 追加** (`Filter.liminf_le_liminf` の `IsCoboundedUnder` 要件、実用 rate-bounded codes で trivial)。新規 plumbing: Pi 化 entropy chain rule (Mathlib + Common2026 両方不在、上流 PR 候補 — Track 3 の `klDiv_pi_eq_n_smul` とペア) → plan: `docs/shannon/aep-source-coding-plan.md` / 実装: `Common2026/Shannon/AEP.lean`
- ~~**AEP Phase E (achievability、rate > H で error → 0)**: typicality 構成。Phase D 完了後の自然な後続。見積 0.5〜1 週間 / 100〜300 行 / 低リスク。~~ → ✅ 完了 (2026-05-11): `Common2026/Shannon/AEP.lean` (+373 行) に Phase A (encoder/decoder via `Finset.equivFin` + `Fin.castLE`、typical set ↔ `Fin M_n`) + Phase B (error rate Tendsto → 0、`typicalSet_prob_tendsto_one` complement squeeze) + Phase C (`codebookSize_log_div_tendsto : Tendsto (fun n => log M_n / n) atTop (𝓝 R)` for `M_n := Nat.ceil (exp (n*R))`、`Real.log_exp` round-trip + `log(1+exp(-nR))` 有界性) + 主定理 `source_coding_achievability` を 0 sorry で実装。`Common2026/Shannon/Bridge.lean` (+9 行) に `entropy_nonneg` 追加 (`[IsProbabilityMeasure μ]` + `Measurable Xs` 仮定、`Measure.isProbabilityMeasure_map` 経由)。両側等号 unified statement (`inf_{achievable codes} liminf (log M_n / n) = entropy μ X`) は Phase F sub-plan に分離 (sInf-over-achievable-codes wrapper +50〜100 行) → plan: `docs/shannon/aep-achievability-plan.md` / 実装: `Common2026/Shannon/AEP.lean` + `Common2026/Shannon/Bridge.lean`
- ~~**Polymatroid structure 化 (Phase D)**: `Polymatroid` structure を導入し本 result をインスタンス化。Mathlib に集合関数版 `Polymatroid` / `Submodular` 不在は inventory 軸 1 で確認済。本 plan は 3 性質単発 theorem で close したので別 plan に切り出した。見積 0〜1 週間 / 50〜200 行 / 低リスク (主に formalism 設計判断)。~~ → ✅ 完了 (2026-05-11): `Common2026/Polymatroid/Basic.lean` (47 行、新ディレクトリ) に `structure Polymatroid (ι : Type*) [DecidableEq ι]` (`rank : Finset ι → ℝ` + 3 axiom: `rank_empty` / `rank_mono : Monotone rank` / `rank_submodular`) を Mathlib `Matroid` style で導入。`entropyPolymatroid : Polymatroid (Fin n)` を `Common2026/Shannon/Polymatroid.lean` (+19 行) に追加し、既存 4 主定理 (`jointEntropySubset_empty` / `_mono` / `_submodular`) で field を充足。新規証明ゼロ、2 ファイル silent → plan: `docs/han/polymatroid-structure-plan.md` / 実装: `Common2026/Polymatroid/Basic.lean` + `Common2026/Shannon/Polymatroid.lean`

### B. 5 シード完了で開いた新シード入口

- **Sanov の定理** (Stein の自然な拡張): `klDiv` の operational meaning を別形 (large deviation principle の rate function) で Lean 化。Stein で立った plumbing (log-likelihood ratio plumbing + Pi 化 chain rule) がそのまま再利用可。
- **Hypercube edge isoperimetry / Han-Bregman bound**: Loomis–Whitney 完了で Shearer の組合せ応用 1 本立った状態。同じ enginer (Shearer) を別 cover で適用するシリーズの第 2 弾。見積 1 週間 / 200〜300 行 / 低リスク。
- **Channel coding theorem (achievability)**: Shannon converse は完了済。achievability 半分 (Cover-Thomas Ch 7 strong typicality + jointly typical decoder) は AEP plumbing 上に構築可能。見積 4〜6 週間 / 800〜1500 行 / 高リスク。

### C. 横断改善

- ~~**`Common2026/Shannon/Pi.lean` に上流 lift 候補 2 件** (Polymatroid 実装で発見): `condEntropy_nonneg` (SlepianWolf / Polymatroid 重複)、`subsetSplitMEquiv` 系 (HanD / Polymatroid 重複)。3 番目の caller が現れた時点で Pi.lean に格上げ。~~ → ✅ 完了 (2026-05-11): `condEntropy_nonneg` + `subsetIdxEquiv` / `subsetSplitMEquiv` / `subsetSplitMEquiv_apply` を `Pi.lean` に lift。SlepianWolf に `import Pi` 追加、HanD / Polymatroid の重複 (含 `condEntropy_nonneg_local`) を撤去。Pi.lean の docstring を「Shannon 共通土台」スコープに更新。
- ~~**`HanD.lean` の Pi reshape を `MeasurableEquiv.piFinsetUnion` ベースに refactor**: Polymatroid inventory で発見、Mathlib 標準補題で自前 `subsetSplitMEquiv` を subsume できる可能性。Han Phase D 周辺の保守ターン候補。~~ → ✅ 完了 (2026-05-11): Mathlib `MeasurableEquiv.piFinsetUnion` ベースの bridge (`coe_piFinsetUnion` / `_apply_left` / `_apply_right`) を `Pi.lean` に追加。`subsetIdxEquiv` + subset-form `subsetSplitMEquiv` / `_apply` を撤去し、`subsetSplitMEquivAux` (disjoint+union 形) に統一。HanD `condEntropy_subset_anti` / Polymatroid 3 sites を aux 直接呼び出しに migrate (各 2 行追加で `Disjoint`/`union` を inline 導出)。net -12 行、3 ファイル全 silent。bridge 3 lemma は upstream 化候補 → plan: `docs/han/hand-pi-refactor-plan.md` / 実装: `Common2026/Shannon/{Pi,HanD,Polymatroid}.lean`

---

## 横断観察 (着手前の整理候補)

- ~~`Common2026/Fano/CondEntropy.lean` (Phase 1 PMF 形) と `Common2026/Shannon/Bridge.lean` (Phase 4-β 測度形) で `entropy` / `condEntropy` が**重複定義**されている。Phase D で再利用が増えた今、どちらかに寄せる整理は次 moonshot 着手前にやる価値あり (再利用コストが今後ボディブローで効く)~~ → ✅ 整理済 (2026-05-10): 調査の結果、両者は厳密には parallel formalism (PMF 形は `μ : α → ℝ` 関数値、測度形は `μ : Measure Ω, Xs : Ω → α`) で相互依存なし。PMF stack (`Fano/Entropy.lean` / `Fano/CondEntropy.lean` / `Fano/Core.lean`) は Phase 1 Fano core proof 専用、Shannon/Han 系列は全て測度形 (`InformationTheory.MeasureFano.condEntropy` + `Shannon.Bridge.entropy`) を使用、新規ムーンショットも測度形に統一する方針。consolidation (PMF Phase 1 を測度形に書き直し) は本来別の大規模 refactor になるためスコープ外。`Fano/Entropy.lean` / `Fano/CondEntropy.lean` 冒頭に formalism boundary docstring を追加して境界を明文化。
- `Common2026/Shannon/` 内の `MeasurableEquiv.piCongrLeft` + `sumPiEquivProdPi` + `funUnique` 3 点セットと `entropy_measurableEquiv_comp` / `condEntropy_measurableEquiv_comp` は Seed 1〜5 全部で再利用される。`Common2026/Shannon/Pi.lean` (仮) に切り出すかは Seed 1 着手時に判断 ✅ 完了 (2026-05-10, 切り出し先: Common2026/Shannon/Pi.lean)

---

## 参照

- 既存 plan:
  - [Fano moonshot](fano/fano-moonshot-plan.md)
  - [Shannon moonshot](shannon/shannon-moonshot-plan.md)
  - [Shannon encoder extensions](shannon/shannon-encoder-extensions-plan.md)
  - [Han moonshot](han/han-moonshot-plan.md)
  - [Han Phase D (subset average / Shearer)](han/han-phase-d-plan.md)
- 5 シード plan (2026-05-10 / 2026-05-11):
  - [Loomis–Whitney moonshot](shannon/loomis-whitney-moonshot-plan.md) ✅
  - [Slepian–Wolf moonshot](shannon/slepian-wolf-moonshot-plan.md) ✅
  - [AEP moonshot](shannon/aep-moonshot-plan.md) ✅ (Phase A〜C / Phase D/E deferred)
  - [Stein moonshot](shannon/stein-moonshot-plan.md) ✅ (Phase A〜B / Phase C/D deferred)
  - [Polymatroid moonshot](han/polymatroid-moonshot-plan.md) ✅ (Phase A〜C / Phase D structure 化 deferred)
- 雛形:
  - [moonshot-plan-template.md](moonshot-plan-template.md)
  - [subplan-template.md](subplan-template.md)

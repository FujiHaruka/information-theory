# Moonshot シードカード集

> **Status (2026-05-10)**: 起草。Fano (測度論版) → Shannon converse (3 形) → Han 補集合形 → Han Phase D (subset average / Shearer) まで sorry ゼロで通った状態を起点に、次のムーンショット候補 5 本をシード化。本ファイルは「どれを次に育てるか」の意思決定用カタログ。
>
> ここに書いてあるのは **着手前の seed**。実装着手の判断 = 該当シードを `docs/<family>/<topic>-moonshot-plan.md` に複製 + `docs/moonshot-plan-template.md` で膨らませる。本ファイル自体はカード一覧として保ち、選定が確定したら該当カードに `→ <plan path>` のポインタを書き加える。

## 起点 (現場実装)

- `Common2026/Fano/Measure.lean` — `fano_inequality_measure_theoretic` (deterministic decoder)
- `Common2026/Shannon/{MutualInfo,DPI,Bridge,CondMutualInfo,Converse}.lean` — KL 主軸 single-shot Shannon converse 3 形 + Markov chain + chain rule
- `Common2026/Shannon/{Entropy,Han,HanD,HanDAverage,HanDShearer}.lean` — 2 変数 / Fin n / Finset (Fin n) の chain rule + conditioning monotonicity + Han 補集合 + Han 1978 subset average + Shearer

このスタックを「異なる角度で擦る」5 本を以下に並べる。

---

## Seed 1: Loomis–Whitney 不等式 🌙

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

---

## Seed 2: Submodularity of entropy / polymatroid axioms

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

---

## Seed 3: Slepian–Wolf 単発 converse 🌙

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

---

## Seed 4: AEP + 源符号化定理（漸近）🌙🌙

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

---

## Seed 5: Stein の補題（仮説検定の最適 error exponent）

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

## 横断観察 (着手前の整理候補)

- `Common2026/Fano/CondEntropy.lean` (Phase 1 PMF 形) と `Common2026/Shannon/Bridge.lean` (Phase 4-β 測度形) で `entropy` / `condEntropy` が**重複定義**されている。Phase D で再利用が増えた今、どちらかに寄せる整理は次 moonshot 着手前にやる価値あり (再利用コストが今後ボディブローで効く)
- `Common2026/Shannon/` 内の `MeasurableEquiv.piCongrLeft` + `sumPiEquivProdPi` + `funUnique` 3 点セットと `entropy_measurableEquiv_comp` / `condEntropy_measurableEquiv_comp` は Seed 1〜5 全部で再利用される。`Common2026/Shannon/Pi.lean` (仮) に切り出すかは Seed 1 着手時に判断

---

## 参照

- 既存 plan:
  - [Fano moonshot](fano/fano-moonshot-plan.md)
  - [Shannon moonshot](shannon/shannon-moonshot-plan.md)
  - [Shannon encoder extensions](shannon/shannon-encoder-extensions-plan.md)
  - [Han moonshot](han/han-moonshot-plan.md)
  - [Han Phase D (subset average / Shearer)](han/han-phase-d-plan.md)
- 雛形:
  - [moonshot-plan-template.md](moonshot-plan-template.md)
  - [subplan-template.md](subplan-template.md)

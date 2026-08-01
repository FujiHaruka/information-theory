# BC 未解決問題 — 候補経路 (層 1)

> 本 relay の主成果物。SoT は経路ごとの記述そのもの。昇格条件 = 親 plan §3.1 の 5 条件、
> 確信度ラベル = §3.2。親 plan: [`bc-open-problem-plan.md`](bc-open-problem-plan.md) /
> 確定事実: [`bc-facts.md`](bc-facts.md) / attack 台帳:
> [`bc-open-problem-attacks.md`](bc-open-problem-attacks.md)
> **本文書が引く数値・記号的検算の再検証**: `python3 docs/shannon/bc-route-r1-check.py`
> (約 9s、`--quick` 0.5s)。乱数種固定・局所最適化不使用ゆえ**再実行で全報告値が一致する**。
> ⚠ `unprobed` の経路を「証明できた」と書かない (親 plan §3.2)。

## 経路一覧

| id | 主張 (1 文) | 軸 | attack slug | 確信度 | 満たす条件 |
|---|---|---|---|---|---|
| R1 | Gohari–Liu–Nair Conjecture 1 (双対汎関数 `F` の加法性) をそのパラメータ `(α, λ)` について一様に仮定し、かつ `F` が Marton 領域の support function の**タイトな**双対であるなら、3 補助変数 Marton 内界の support function は同一チャネルの自己テンソルに対して加法的 (`h_n^T(θ) = n·h_1^T(θ)`, ∀`n`, ∀`θ ≥ 0`) である | E+G | `support-vs-dual-additivity` | `unprobed` (含意は文献で確認済) | (1)(2)(3) / **(5) novelty gate 不合格 (L8)** |

**R1 は (5) novelty gate を通らなかった。経路として昇格しない。**
L8 が一次文献 3 本を逐語取得した結果、**R1 の 12 step は 1 本残らず出典が付いた** — 主要な出所は
Anantharam–Gohari–Nair (IEEE TIT 65(3), 2019、以下 [AGN19]) の式 (2) / (9)(10)(11) / (20)(21)(22) +
Lemma 2、Gohari–Liu–Nair (ISIT 2025、以下 [GLN25]) の式 (1) + Appendix、Nair (ITA 2020、以下 [N20])
の式 (1)(2) + Definition 1.4。**含意としては 1 step も落ちていない (R1 は正しい)** が、新規性はゼロで
ある。対応表と逐語は [`bc-facts.md`](bc-facts.md) §L8 の (iv) 行。
本文書は**その判定を反映した後の姿**として残す — R1 は経路ではなく、「軸 E の開いている場所が
どこか」を逐語出典つきで確定させた**地図**である (→「L8 後に残るもの」)。

---

## R1 — `F` は「`{a_x}` ↔ `θ` の Legendre」ではなく `min_α max_p min_a` の 3 段入れ子の中段である

### 主張 (条件 1)

有限アルファベットの DM-BC `T(y,z|x)` と 3 補助変数 Marton 内界 `M(T)` (= Jog–Nair Bound 1、
私信のみ、補助 `(U,V,W)`) について、次の 3 つを仮定する:

- **(H1)** Gohari–Liu–Nair Conjecture 1 (Additivity Conjecture) が `F` の内部パラメータ
  `(α, λ)` の**すべての値について**成り立つ。**⟹ L8 でこの読みが正しいことを確定** (facts §L8 (i))。
  未解決の予想そのものなので、依然として仮定である。
- **(H2)** step 6 のタイトさ — `F` から作る双対値 `h̄` が `M(T)` の support function `h^T` に一致する。
  **⟹ L8 で仮定ではなく既知の定理と判明** ([GLN25] 式 (1)、Appendix A に証明。facts §L8 (ii))。
- **(H3)** `M(T)` が閉凸である (support function が集合を決めるために要る)。
  **⟹ L8 で [AGN19] が地の文で主張していることを確認** (証明は付いていない。facts §L8 (vi))。
  ⚠ **我々の 2 補助変数 `def` の凸性は依然未証明** (facts V5) — これは別の対象。

このとき `h_n^T(θ) := sup_{R ∈ M(T^{⊗n})} θ·R` は **`h_n^T(θ) = n·h_1^T(θ)` を全 `n ≥ 1` /
全 `θ ∈ ℝ²₊` で満たし**、外部ノートの同値条件 (3) により `C(T) = M(T)` が従う。

⚠ **R1 は Conjecture 1 を証明しない**。R1 は含意 (conditional statement) であり、(H1) は未解決の
予想そのものである。R1 の内容は「(H1) から (3) へ至る導出を明示的に書き下すこと」— それが
attack `support-vs-dual-additivity` の標的だった (facts §L2 の最終行)。

### 記法と前提

| 記号 | 意味 | 出所 |
|---|---|---|
| `T(y,z\|x)` | 有限 DM-BC。`X,Y,Z` は有限 | — |
| `M(T)` | **3 補助変数** Marton 内界 (私信のみ)。制約 4 本は下の `A₁,A₂,S₁,S₂` | facts F2 の Jog–Nair Bound 1 逐語 |
| `h^T(θ)` | `sup_{R ∈ M(T)} θ·R`、`θ ∈ ℝ²₊`。`h_n^T(θ) := h^{T^{⊗n}}(θ)` | 外部ノート (2) |
| `F(T,{a_x})` | 双対汎関数。内部パラメータ `(α, λ)` | facts §L8 (ii) の [GLN25] 原文逐語 (**エントロピー項は `−αH(Y) − (λ−α)H(Z)`**。V7 の転記 `(1−α)` は誤りで L1 (b) ④ の訂正が正しかった) |
| **`μ`** | **`F` の内部パラメータ `λ` を本文書ではこう書く** | 下記 ⚠ |
| `α` | `F` のもう 1 つの内部パラメータ | 同上 |
| `martonRegionUnion` | **我々の Lean `def`。2 補助変数、共通補助 `U₀`/`W` を持たない** | `InformationTheory/Shannon/BroadcastChannel/MartonUnion.lean` |

⚠ **`λ` が 3 つ衝突する**ので本文書では次のように呼び分ける:
(i) 領域側の方向 `θ = (θ₁, θ₂)`、(ii) 外部ノートの `λ-SRM` の `λ` (= 本文書の `α`)、
(iii) `F` の定義中の `λ` (= 本文書の `μ`)。step 2 で (ii) と (iii) が**別物であること**が
導出される (両方が同時に `F` に現れる)。

⚠ **在庫との差 (最重要の前提)**: 我々の `martonRegionUnion` は **2 補助変数版**で共通補助を持たない
(`MartonUnion.lean` の module docstring が逐語 "Convexity is claimed of the quadrilaterals only,
not of the union")。**R1 は 3 補助変数版 `M(T)` についての経路であり、我々の Lean `def` の上では
述べられない** — `W` が経路の中核 (step 3 の上凹包) を担うため。前提工事
`marton-3aux-probe` は R1 によって不要になるのではなく、**R1 が何を作るべきかを指定する**
(→「この経路が通ると何が言えるか」)。

**`M(T)` の 4 制約** (facts F2 の Jog–Nair Bound 1 逐語、`Y₁ = Y`, `Y₂ = Z`):

```
A₁ = I(U,W;Y)                                  R₁ ≤ A₁
A₂ = I(V,W;Z)                                  R₂ ≤ A₂
S₁ = I(U,W;Y) + I(V;Z|W) − I(U;V|W)            R₁+R₂ ≤ S₁
S₂ = I(V,W;Z) + I(U;Y|W) − I(U;V|W)            R₁+R₂ ≤ S₂
```

`θ` は受信者ラベルの入替で **`θ = (1, μ)`, `μ ≥ 1`** と正規化してよい (以下この形で書く)。

### ステップ (条件 2 + 3)

| # | 中間命題 | 入力 | 出力 | ラベル | 根拠 / 出典 |
|---|---|---|---|---|---|
| 1 | 四辺形の support function は 1 パラメータの双対 `h_{Poly(p)}((1,μ)) = min_{σ∈[0,μ]} φ(σ)`, `φ(σ) = (1−σ)⁺A₁ + (μ−σ)⁺A₂ + σ·min(S₁,S₂)` | Bound 1 の 4 制約 + `R ≥ 0` | `σ` (総和レート乗数) の 1 次元 min | `known` | 線形計画双対定理 (標準結果、逐語出典は不要と判定)。**L8: 経路上の実体は [AGN19] 式 (2) の第 3 行** — 逐語 `= max_{p(u,v,w,x)} min_{λ∈[0,1]} (δ₁+λ(δ₀+γ₂))I(W;Y) + (1−λ)(δ₀+γ₂)I(W;Z) + …` で、`min{a,b} = min_{λ∈[0,1]} λa + (1−λ)b` を使う段がそのまま置かれている。本 leg (L7) で数値確認 = ランダム 4000 形で primal (HiGHS) と `min_σ φ` の不一致 **0/4000**。`φ` は `σ` について区分線形で折れ点は `{1, μ}` のみゆえ端点込み 3 点評価で厳密。肯定コントロール 3 本 (弱双対性 / 閉形式 primal との独立照合 / 折れ点集合の完全性) も 0 違反。**再検証 → check スクリプト §2** |
| 2 | **`σ = 1` を固定し `(s₁,s₂) = (α, 1−α)` と分割した双対値が `F` の被積分量そのもの**: `(μ−1)A₂ + αS₁ + (1−α)S₂ = α·I(W;Y) + (μ−α)·I(W;Z) + I(U;Y\|W) + μ·I(V;Z\|W) − I(U;V\|W)` | step 1 | `α` の正体 = **総和レート制約 2 本への乗数の配分**、`μ` の正体 = **方向 `θ` そのもの** | `new` | **記号的に証明** (係数相殺)。両辺は `(α,μ)` についてアフィンなので 5 点で恒等。同時に `y₁ = 0`, `y₂ = μ−1 ≥ 0`, `s₁+s₂ = 1` が**一意に決まる**ことも導出。再検証 → 下記「検算」 |
| 3 | **`W` の消去 = 入力単体上の上凹包**: `I(W;·) = H(·) − H(·\|W)` で分解すると step 2 の量は `α·H(Y_p) + (μ−α)·H(Z_p) + E_W[G_{α,μ}(p_W)]` になり、`W` 分解にわたる sup は `conc(G_{α,μ})(p)`。ここで `G_{α,μ}(q) := max_{(U,V): 入力周辺 = q}[I(U;Y)+μI(V;Z)−I(U;V)] − α·H(Y_q) − (μ−α)·H(Z_q)` | step 2 | `W` が消え、残るのは `Δ(X)` 上の上凹包 | **`known` (L8 で確定)** | **[AGN19] 式 (2) のステップ (c) そのもの** — 逐語 "Equality (c) follows from the interpretation of auxiliary variables in terms of upper concave envelopes as presented in [16]" (= Nair, *Upper concave envelopes and auxiliary random variables*, Int. J. Adv. Eng. Sci. Appl. Math. **5**(1):12–20, 2013)、および **Remark 1 逐語** "It is useful to note that the random variable W plays the role of mixing between various distributions of p(u, v, x), to achieve the concave envelope."。[GLN25] Appendix も逐語 "where C{} is the upper concave envelope"。**凹化する対象がエントロピー項を含む点も原文で確認** — [AGN19] の `t_λ(X)` は `I(X;Y)` / `I(X;Z)` 項を含んだ形で定義されている (`H` 形との差は `p(x)` について線形ゆえ `{a_x}` に吸収される)。分解自体は L7 が記号的に確認済 (下記「検算」) |
| 4 | **`{a_x}` は入力周辺 `p(x)` の Fenchel 共役変数**: `F(T,{a};α,μ) = max_{q∈Δ(X)}[G_{α,μ}(q) + ⟨a,q⟩]`、ゆえに `conc(G_{α,μ})(p) = min_a [F(T,{a};α,μ) − ⟨a,p⟩]` | step 3 | `{a_x}` の正体 | `known` | Fenchel–Moreau (双共役) をコンパクト凸集合 `Δ(X)` 上で適用。**L8: [AGN19] 式 (9)(10)(11) が逐語**で `f†(d) = max_{p(x)}{f(p(x)) − Σ_x d_x p(x)}` / `C[f](p(x)) = inf_d {f†(d) + Σ_x d_x p(x)}` を置き、"Two properties that we exploit are that (i) the dual of a function f is the same as the dual of C[f]; (ii) the dual of f uniquely determines C[f]." と述べる。[GLN25] Appendix も逐語 "By convex duality, we have"。`F` の被最大化量が `G_{α,μ} + ⟨a,·⟩` に一致することは記号的に確認済 (facts L1 (b) ⑤(b) の展開式とも一致) |
| 5 | **min と max を交換できる**: `Ĝ(p,α) := α·H(Y_p) + (μ−α)·H(Z_p) + conc(G_{α,μ})(p)` は `p` について凹 / `α` について凸 ⟹ `sup_p min_α = min_α sup_p`。`Λ_{α,μ}(T) := max_{p∈Δ(X)} Ĝ(p,α)`, `h̄_μ(T) := min_{α∈[0,1]} Λ_{α,μ}(T)` | step 3, 4 | 3 段入れ子 `min_α max_p min_a` の確定 | `known` | ミニマックス定理。凹性: エントロピーは線形像について凹 + `conc` は凹。凸性: `conc` は `α` についてアフィンな族の sup ゆえ凸。**L8 で出典が付き、しかも Sion ではなかった** — [AGN19] 式 (2) のステップ (b) が逐語 "Equality (b) follows by an application of Corollary 2 in [3] which, in turn, follows using a **max-min theorem of Terkelsen** [18]" (F Terkelsen, *Some minimax theorems*, Mathematica Scandinavica **31**:405–413, 1972 / [3] = Geng–Gohari–Nair–Yu, IEEE TIT **60**(1):22–41, 2014)。[GLN25] Appendix は逐語 "(a) follows by a min-max exchange [5]" |
| 6 | **タイトさ (H2)**: `h̄_μ(T) = h^T((1,μ))` は「`h̄` の最大化点で `min(S₁,S₂) ≥ A₂`」と**同値**。⚠ **自動では成り立たない** | step 1, 5 | (H2) の必要十分条件 | **`known` (L8 で確定)** | **step 6 は [GLN25] 式 (1) そのもの** — 逐語 `Γ^λ_M(T) = min_{α∈[0,1]} max_{p(x)} [αH(Y) + (λ−α)H(Z) + min_{a_x}(F(T,{a_x}) − Σ_x p(x)a_x)]` で **`=` であって `≤` ではなく**、直後に "We provide a proof of the above equation in Appendix A for completeness." と書かれている。左辺 `Γ^λ_M(T) = max_{(R₁,R₂)∈R_M} R₁ + λR₂` は `M(T)` の support function を方向 `(1,λ)` で評価したもの ⟹ **`h̄_μ(T) = h^T((1,μ))` は文献の定理**。**L7 が「残余」とした `S₁ ≥ A₂` は [AGN19] が `[·]₊` の切断で処理済** — 逐語 "the rate triple given by `R₀ = 0`, `R₁ = I(U, W;Y)`, and `R₂ = [min{I(W;Y), I(W;Z)} + I(U;Y\|W) + I(V;Z\|W) − I(U;V\|W) − I(U, W;Y)]₊` belongs to R_M" (達成側は切断つきの頂点、上界側は切断なしの線形計画緩和という 2 方向の議論)。**[GLN25] が `[·]₊` を落として書いているのが L7 の誤検出の原因**で、原典にその粗さは無い (facts §L8 (vii))。以下は L7 の記録 (判定としては上書きされたが、`σ=1` 層が自動では緩くない事実の測定として残す): 同値性は数値で確認 (述語一致 **0/2000 不一致**)。⚠ 抽象的な四辺形の形をランダムに振ると `σ=1` は **1417/2000 で真に緩い** (最大ギャップ `5.15`)。**討ち取った半分**: 最大化点では必ず `S₂ ≥ A₂` (もし `I(U;Y\|W) < I(U;V\|W)` なら `U` を定数にすると `A₂` 不変・`min(S₁,S₂)` 増大で目的値が**真に増える**ので矛盾) — ランダム同時分布 800 本で該当標本 776 本すべてが真に増加、肯定コントロール 2 本 (摂動が `A₂` を厳密に保つ / 摂動後 `S₂ = A₂`) も 0 違反。**残余**: `S₁ ≥ A₂`, すなわち `I(W;Y) − I(W;Z) ≥ I(U;V\|W) − I(U;Y\|W)` を最大化点で示すこと。**再検証 → check スクリプト §3 (述語) / §4 (部分証明)** |
| 7 | **(H1) ⟹ 上凹包の劣加法性**: 任意の `p ∈ Δ(X₁×X₂)` (**相関のあるものを含む**) で `conc(G^{T₁⊗T₂})(p) ≤ conc(G^{T₁})(p₁) + conc(G^{T₂})(p₂)` | (H1), step 4 | 積チャネル側の上界 | `new` | `min_a` を分離可能な `a_{x₁}+b_{x₂}` に制限すると上界になり、`⟨a⊕b, p⟩ = ⟨a,p₁⟩+⟨b,p₂⟩` は `p` が相関していても周辺だけで決まる ⟹ Conjecture 1 がそのまま効く。**Conjecture 1 が「分離可能な `a` に限る」ことがここで初めて効く** |
| 8 | エントロピー項も劣加法: `α·H(Y₁,Y₂) + (μ−α)·H(Z₁,Z₂) ≤ Σᵢ [α·H(Yᵢ) + (μ−α)·H(Zᵢ)]` | `α ∈ [0,1]`, `μ ≥ 1` | 同上 | `known` | エントロピーの劣加法性 (標準結果、逐語出典は不要と判定)。係数の非負性 `α ≥ 0`, `μ−α ≥ 0` が要る。**L8: 範囲 `α ∈ [0,1]` / `λ ≥ 1` は 3 本すべてで明示されている**ので、この非負性は文献の設定内で満たされる (facts §L8 (iii))。step 7+8+9 をまとめた形が [GLN25] p.2 の sub-additivity display と [AGN19] 式 (21)→(22)→Lemma 2 |
| 9 | **各 `(α,μ)` で `Λ` は加法的**: `Λ_{α,μ}(T₁⊗T₂) = Λ_{α,μ}(T₁) + Λ_{α,μ}(T₂)` | step 7, 8 | `≤` はそこから、`≥` は積分布 + 積補助変数から | `new` | 機械的。`≥` 側: `p = q₁⊗q₂`, `U=(U₁,U₂)`, `V=(V₁,V₂)`, `W=(W₁,W₂)` を独立に取ると全項が分離 |
| 10 | **`min_α` の段 — ここが経路の核**: `h̄_μ(T^{⊗n}) = min_α Λ_{α,μ}(T^{⊗n}) = min_α [n·Λ_{α,μ}(T)] = n·min_α Λ_{α,μ}(T) = n·h̄_μ(T)`。**自己テンソルだから通る** | step 9 | `h̄` の自己加法性 | **`known` (L8 で確定)** | `min` は加法的でないが、**同一関数の `n` 倍**に対しては可換 (`min_α n f(α) = n min_α f(α)`)。⚠ `T₁ ≠ T₂` では `min_α[f+g] ≥ min_α f + min_α g` の**一方向しか出ない** — 下記「この経路が通ると何が言えるか」の (b)。**L8: この非可換性の観察は正しく、しかも文献が既に踏まえている** — [AGN19] 式 (20) は `min_λ` を**両辺の外に置いたまま** 1 文字と (1/2)×2 文字の**自己テンソル**を比べ、[N20] 式 (1) も `M̂c(W_a ⊗ W_a, W_b ⊗ W_b) = M̂c ⊕ M̂c` と自己テンソルに限定し、[N20] Remark 1.3 は逐語 "This statement is slightly more general than is needed to establish (1). On the other hand such a statement with non-identical components will be useful as can be seen later in this article." と `T₁ ≠ T₂` 版が過剰であることを明言する。⚠ **[GLN25] p.2 の display だけが `min_{α∈[0,1]}` を 2 つに割っており、その最終段は `T₁ ≠ T₂` では従わない** — ただし容量に要るのは自己テンソルだけなので論文の結論は壊れない (facts §L8 (v))。⟹ **step 10 に残っていた新規性は「二次文献の書き方の粗さの指摘」でしかない** |
| 11 | (H2) を使って `h̄` を `h` に置き換え: `h_n^T(θ) = n·h_1^T(θ)`, ∀`n`, ∀`θ ≥ 0` | step 6, 10 | 外部ノート (3) の左辺 | **`known` (L8 で確定)** | step 6 が既知の定理になったので条件つきではなくなった。**[AGN19] 式 (20) が逐語**: "Marton's inner bound is optimal **if and only if** for every channel p(y, z\|x) and for any δ₁, δ₀, γ₂ ≥ 0, the following equality holds" に続けて `min_{λ∈[0,1]} max_{p(x)}[…] = (1/2) min_{λ∈[0,1]} max_{p(x₁,x₂)}[…]`。⚠ **自己テンソルであることは逐語ではなく読み** — 主文が単数の "for every channel p(y, z\|x)" で係数が `1/2` ゆえ 2 文字拡大と読む (facts §L8 (iv) に留保つきで記録)。自己テンソル限定を**逐語で明示している**のは [N20] 式 (1) の側 |
| 12 | `h_n = n·h_1` ∀`n`,`θ` ⟹ `C(T) = M(T)` | step 11, (H3) | 結論 | **`known` (L8 で確定)** | 外部ノート (1)(2)(3) の実体は **[N20] 式 (1)** = 逐語 "`M̂c(W_a ⊗ W_a, W_b ⊗ W_b) = M̂c(W_a, W_b) ⊕ M̂c(W_a, W_b), ∀W_a, W_b`" (`⊕` = Minkowski 和) + Remark 1.2 逐語 "This follows from the fact that n-letter extension of Marton's region tends to capacity from which the above condition for optimality is rather immediate."。**(H3) `M(T)` の閉凸性は [AGN19] が地の文で主張している** — 逐語 "Since Marton's achievable region is a convex set in R³₊ the region can be characterized by determining the supporting hyperplanes" (⚠ 証明は付いていない。facts §L8 (vi)) ⟹ **L7 が置いた `gap` は文献の側では開いていない**。⚠ **ただし我々の 2 補助変数 `def` の凸性は依然未証明** — facts V5 の判定は動かない (対象が違う)。3 補助版 `M(T)` については在庫に主張自体が無い。⚠ **この gap は step 12 に局在する** — step 1–11 の橋は閉凸性を一切使わない (support function は集合の閉凸包しか見ないので、橋の側は閉凸包の言葉で完結する) |

**検算 (本 leg で実行した記号的確認 — 掃引ではなく係数相殺 = 証明)**:
step 2 / 3 / 4 の恒等式と `M(T)` の 4 制約まわりの関係式 (`S₁ − A₁`, `S₂ − A₂`, `A₁+A₂−S₁`,
`A₁+A₂−S₂`, および step 6 の残余条件 `S₁ − A₂ = I(W;Y) − I(W;Z) + I(U;Y|W) − I(U;V|W)`) を
[`bc_probe.py`](bc_probe.py) の `prove_identity` で残差係数が全消去することを確認
(16 項目すべて PASS)。step 1 / 6 の線形計画部分は数値 (上表に記載)。`(α,μ)` について両辺は
アフィンなので有理点 5 つで恒等が従う。
**再検証コマンド**: `python3 docs/shannon/bc-route-r1-check.py` (§1 が記号、§2–§4 が数値。
約 9s、`--quick` 0.5s)。乱数種は固定してあり、**局所最適化を一切使っていないので報告値は
再実行で一致する** (2 回実行の出力が実行時間行を除いて完全一致することを確認済)。
⚠ **このスクリプトは R1 の主張そのものを probe しない** — 振っているのは四辺形の形
`(A₁,A₂,S₁,S₂)` であって実在チャネルの最大化点ではないので、§3 の「緩む割合」は
実チャネルでの頻度を意味しない。実チャネル上の判定は L8 の P2。

### 仮説の性質 (親 plan §5-8)

| 前提 | 分類 | 経路上のどこに出ているか |
|---|---|---|
| 有限アルファベット `X, Y, Z` | **precondition** (正則性) | 記法の節 |
| 濃度限界 `\|U\|+\|V\| ≤ \|X\|+1`, `\|W\| ≤ \|X\|+4` | **precondition** (`G_{α,μ}` の達成可能性 / 連続性のため) | step 3, 4。出典 = Mar-Con.pdf §I 逐語 (facts L1 (b) ⑥ に転記済) |
| `μ ≥ 1` / `θ ∈ ℝ²₊` | **precondition** (受信者ラベル入替で WLOG) | 記法の節 |
| **(H1) Conjecture 1 が `(α,μ)` について一様** | **load-bearing** | **step 7 の入力として明示**。R1 は (H1) からの含意であり (H1) を証明しない。**L8 でこの読みが正しいことを確定** — 量化子は Conjecture 1 の文そのものには無い (記法 `F(T,{a_x})` が `(α,λ)` を落としている) が、**[N20] が同じ対象を `F₁^{(λ,α)}` と上付きで書き "For λ ≥ 1 and α ∈ [0,1], define the following" と量化したうえで加法性を `∀η, ζ` で述べ Definition 1.4 "global tensorization property" と名付けている**。加えて [GLN25] 自身が `min_{α∈[0,1]}` の**内側で** Conjecture 1 を適用している ⟹ **弱い読みは文献の読みではない** (facts §L8 (i)) |
| **(H2) `F` 双対のタイトさ** | ~~load-bearing~~ → **既知の定理** | step 6。**L8 で [GLN25] 式 (1) + Appendix A と判明したので仮定ではない** (facts §L8 (ii)) |
| **(H3) `M(T)` の閉凸性** | ~~load-bearing~~ → **文献の言明** | step 12。**L8 で [AGN19] §I-B の地の文と判明** (証明は付いていない ⟹ 完全な `machine` 確定ではない。facts §L8 (vi)) |

**核を前提に押し込んでいないことの確認**: (H1)(H2)(H3) はいずれも上表の step の**入力または
ラベル付きステップ**として本文に出ており、ラベルが表示されている。R1 が主張するのは
これらを仮定したときの含意だけである。**L8 後は (H2)(H3) が文献側で閉じ、残る仮定は (H1) =
Conjecture 1 そのもの 1 本になった** — すなわち R1 は「未解決の予想を仮定すれば未解決問題が解ける」
という、**文献が既に持っている含意**に収束した。

### L8 後に残るもの

**(a) facts §L2 が「どちらの文献も供給していない」と確定させた 2 段は、実は**両方とも供給されていた**。**
L2 は (a) `M` の閉凸性 / (b) `{a_x}` と `θ` を結ぶ双対の段の 2 つを挙げて「どちらの文献も供給して
いない」と書いたが、**L8 が原典 [AGN19] を取得した結果、(a) は §I-B の地の文 (facts §L8 (vi))、
(b) は式 (2) + (9)(10)(11) (同 (iv)) として供給されていた**。L2 の判定が誤ったのは**二次文献
([GLN25]) だけを読んでいたため**で、L2 の時点で原典は未取得だった。
⟹ attack `support-vs-dual-additivity` の標的は**文献の側では最初から閉じていた**。

**(b) facts ① の「同一命題ではない」に構造的な理由がつく。**
facts が挙げた 3 つの食い違いは、この経路の上では 1 点に集約される:

- `F` の加法性は **`σ = 1` を固定し `(α,μ)` を固定した層**での主張。
- support function の加法性は **`min_α` を取った後**の主張。
- `min_α` は**同一チャネルの自己テンソルに対しては透過**だが (step 10)、`T₁ ≠ T₂` では
  `≥` しか出ない。

⟹ **Conjecture 1 が `T₁ ≠ T₂` を許すのに、異なる 2 チャネルの積で Marton 領域が
Minkowski 和より真に大きい例が既知である**という一見した緊張は、**`min_α` の段でちょうど
解消される** (両者は矛盾しない)。この整合が経路の内部整合性の証拠になっている
(外部ノート (11) 直下の注意書き / facts F5 の非因子分解と衝突しない)。

**(c) 外部ノートの否定側 (11) が「どこを壊せばよいか」に翻訳される。**
step 1–11 が正しければ、自己テンソルで `h_n > n·h_1` を出すことは (H1) または (H2) の反証と
同値になる。しかも step 7 より、(H1) の破れは**分離可能でない `a`** では起こりえない
(Conjecture 1 は分離可能な `a` しか主張していないが、step 7 が要求するのも分離可能な `a` だけ)
⟹ **反例を探す場所は `(α,μ)` 平面上の Conjecture 1 の破れか、step 6 のタイトさの破れの 2 つに絞られる**。

**(d) `markovity-via-dual-F` (軸 G) の park が解ける方向を指す。**
L5 で M2 が偽になったのは共通補助 `W` を落としたからだった (facts §L5 の 2 行目)。R1 は
**`W` がどこで効いているか**を step 3 (上凹包) として特定するので、Conjecture 2 を領域側 `h`
ではなく双対側 `F` の言葉で扱う受け皿ができる。

**(e) 前提工事 `marton-3aux-probe` の仕様が決まる。** R1 は 3 補助版 `M(T)` の話なので、我々の
Lean `def` の上では述べられない。しかし R1 は**何を作ればよいか**を指定する — probe 側に要るのは
「`W` を持つ領域」ではなく「`Δ(X)` 上の `G_{α,μ}` とその上凹包」1 本である (step 3)。

⚠ **通っても未解決問題は解けない、かつ新規性もゼロである**。(H1) は未解決の予想であり、
[GLN25] の Conclusion が逐語で "Even if one can prove the additivity within this class …, one
would have shown that Marton's region is the capacity region." と述べている以上、
**「(H1) ⟹ Marton = 容量」という含意自体は著者らが既に持っている** (facts V7)。**L8 が原典まで
遡った結果、L7 が新規性の候補として残した step 6 と step 10 も既知だった** ⟹ **R1 に主張できる
新規性は 1 つも無い**。R1 が残す価値は次の 3 点に限られる:

1. **軸 E で開いている場所の確定** — (H1) = Conjecture 1 だけが未解決で、それ以外の 11 step は
   すべて文献にある。⟹ **軸 E で新規性を主張しうるのは Conjecture 1 の証明か反証だけ**。
2. **反例を探す場所の絞り込み** ((c) 節) が、既知の枠組みの上での正しい絞り込みだと確認された。
3. **記号的検算 16 項目** — 文献の等式を我々の記法で独立に再導出した記録として残る (誤りは
   出なかった)。「二次文献の転記から出発して原典の式を復元できた」ことの確認でもある。

### 未達の条件と次の一手

#### (4) probe — 4 本のうち **P1 は実施済 (L8)。P2 は目的が消えた。P3 / P4 は生きている**

**P1 (実施済 — L8)**。取得した一次文献 3 本と 3 点の判定は
[`bc-facts.md`](bc-facts.md) §L8 (逐語つき 7 行)。要点だけ:

- **(i) 量化子** — **一様な読みが正しい** ((H1) の読みは生きている)。ただし量化子は Conjecture 1 の
  文そのものには無く、[GLN25] §I の "For any λ ≥ 1" と式 (1) の `min_{α∈[0,1]}`、論文自身が
  `min_{α∈[0,1]}` の内側で Conjecture 1 を適用していること、そして決定打として **[N20] が同じ対象を
  `F₁^{(λ,α)}` とパラメータ明示で書き "For λ ≥ 1 and α ∈ [0,1], define the following" と量化する**
  ことによる。⟹ **step 9→10 は (i) では死なない**。
- **(ii) `F` ↔ Marton 領域** — **述べられており、しかも等号 (タイト)**。[GLN25] 式 (1) + Appendix A、
  出所は [AGN19] の convex duality。⟹ **step 6 は既知**。
- **(iii) 範囲** — **3 本すべてで明示**。
- **副産物 3 件** — (H3) 閉凸性は [AGN19] の地の文にある / L7 が step 6 の残余とした `S₁ ≥ A₂` は
  [AGN19] が `[·]₊` の切断で処理済 / [GLN25] の `F` のエントロピー係数は `(λ−α)` (facts V7 の転記誤り
  を原文で確定)。

**P2 (取り下げ — 目的が消えた)**。設計していたのは step 6 のタイトさの数値 probe だが、step 6 は
[GLN25] 式 (1) として既知で、L7 が「残余」とした `S₁ ≥ A₂` は [AGN19] の `[·]₊` 切断で処理済
(facts §L8 (vii)) ⟹ **確かめるべき未決の命題が無い**。⚠ **設計そのものは捨てない** — 「2 つの下界を
比べる設計にしてはならない / 同一の `p` の上で述語だけを見る」という誤差の向きの規律 (下記) は、
`marton-3aux-probe` や `selftensor-counterexample` で 3 補助版を数値で触るときにそのまま要る。
以下は取り下げた設計の記録:

- チャネル: `|X| = 3`, `|Y|,|Z| ∈ {2,3}`、Dirichlet 濃度 `0.3 / 3.0` で 20 本 (L5 の
  [`bc-markovity-conjecture-check.py`](bc-markovity-conjecture-check.py) の生成器を再利用)。
  加えて **facts §L5 の `W1_CEX` / `W2_CEX`** (M2 の反例チャネル) を必ず含める。
- 補助: `|U|,|V| ≤ 4` (濃度限界 `|X|+1 = 4`)、`|W| ≤ 7` (`|X|+4`)。
- `μ ∈ {1, 1.25, 1.5, 2, 3, 5}`。
- 目的量: `Ψ(p) := (μ−1)·A₂(p) + min(S₁(p), S₂(p))` を `p(u,v,w,x)` 上で最大化し、
  **最大化点で `S₁ ≥ A₂` が成り立つかを記録する**。
- **判定**: `S₁ < A₂` となる最大化点が 1 つでも出れば **step 6 は偽 ⟹ R1 は書き直しが要る**
  (退路 = `θ` を `F` 双対がタイトな方向に限定して主張を弱める)。全件で `S₁ ≥ A₂` なら step 6 は
  probe を通過。
- **⚠ 誤差の向き (L5 の注記が効く場所)**: `Ψ` も `h` も局所最適化が返すのは **sup の下界**なので、
  2 つの下界の差には符号保証が無い。**したがって「`Ψ` の値と `h` の値を比べる」設計にしてはならない**。
  上の設計は**同一の `p` の上で述語 `S₁ ≥ A₂` を見る**だけなので、この罠を踏まない。これが P2 の
  設計上の要点。
- **肯定コントロール 2 本**: (i) `U` を定数にした点では `S₂ = A₂` が厳密に成り立つ
  (step 6 の部分証明の帰結) — 判定器のバグ検出。(ii) 劣化 BSC 対 (`q=0.1`, `p=0.25`) で
  `W` を定数にすると 2 補助版に落ち、facts V5 の閉形式 `λI₁+(1−λ)I₂−min(λ,1−λ)I₁₂` と一致する。

**P3 (生きている、しかも L8 で主語が強くなった)**。`|X| = 2` (⟹ `|X²| = 4`) で
`conc(G^{T⊗T})(p)` を単体グリッド上の総当たり上凹包で直接計算し、相関のある `p` について
`conc(G^{T⊗T})(p) ≤ conc(G^T)(p₁) + conc(G^T)(p₂)` を検定する。**破れが出れば Conjecture 1 の
反例**。肯定コントロール: `p = q⊗q` で両辺が一致すること。
**L8 の発見**: この検定は **[AGN19] の式 (22) の破れの探索そのもの**で、同論文が Lemma 2 で双対形
(`F(T₁,{a}) + F(T₂,{b}) < F(T₁⊗T₂,{a+b})`) に書き換えたうえで実際に走らせている。結果は逐語
"At least when all outputs of both broadcast channels are binary valued, we believe that we
performed a rather exhaustive and intensive search, yet we were unable to find any such instance."
**そして著者らが逐語で独立再現を求めている**: "since this is a rather central problem in network
information theory, we would also urge other interested researchers to **independently confirm our
numerical observations**." ⟹ **P3 は「新しい問い」ではないが、著者自身が公開で要請している
独立再現**であり、軸 E で実際に着手できる作業として残る。⚠ 設計上の注意 2 点 — (a) [AGN19] は
`|U| = 2, |V| = 3` と `|U| = 3, |V| = 2` を逐語で "the main nontrivial cases" と名指しているので
そこを外さない、(b) 探索空間は原論文の Proposition 3 / 一般化 AND・XOR パターンの排除で大幅に
削れる (同論文が手順を書いている)。

**P4 (価値が下がった)**。`argmin_α Λ_{α,μ}(T₁) ≠ argmin_α Λ_{α,μ}(T₂)` となる 2 チャネルを実際に
出す probe。L8 で step 10 の非可換性は文献が既に踏まえていると確認された ([N20] Remark 1.3 が
逐語で `T₁ ≠ T₂` 版は "slightly more general than is needed") ので、**確かめても既知の再確認に
しかならない**。⚠ ただし [GLN25] p.2 の display はこの段を割って書いているので、**その粗さが
実チャネルで実際に効くことを 1 例で示す**なら意味はある (優先度は最低)。

#### (5) novelty gate — 実施結果 (L8)

**判定: R1 は通らなかった。** 4 項目の結果:

1. **[AGN19] を取得済** (`https://chandra.ie.cuhk.edu.hk/pub/papers/BC/Marton-update.pdf`、8 頁)。
   結果は予想を超えて広く、**step 1–6 だけでなく step 7–12 も既出**だった (facts §L8 (iv) の対応表)。
   step 6 = [GLN25] 式 (1)、step 11+12 = [AGN19] 式 (20) の "if and only if"。
2. **`"concave envelope" + Marton + auxiliary W` = 既知、逐語出典あり**。[AGN19] 式 (2) ステップ (c)
   + **Remark 1** 逐語 "the random variable W plays the role of mixing between various distributions
   of p(u, v, x), to achieve the concave envelope"、出所は Nair, *Upper concave envelopes and
   auxiliary random variables*, Int. J. Adv. Eng. Sci. Appl. Math. **5**(1):12–20, 2013。
   ⚠ **「常識だろう」で落としたのではなく逐語で落とした** (親 plan §5-7 の逆向き義務)。
3. **`"additivity" + "support function" + "Marton" + "tensor power"` — WebSearch 2 クエリで打ち切り**。
   一般検索では step 10 の `min_α` 非可換性を名指す文献に当たらなかったが、**著者ページの
   [N20] を直接取得したことで決着した** — [N20] 式 (1) が自己テンソルに限定した形で書かれ、
   Remark 1.3 が `T₁ ≠ T₂` 版は必要以上に強いと逐語で述べている。⟹ **検索は打ち切ったが判定は
   `known`**、根拠は一般検索ではなく一次文献の逐語。
4. **[GLN25] Conclusion との差分 = ゼロ**。逐語 "Even if one can prove the additivity within this
   class (without needing to prove the conjecture), one would have shown that Marton's region is
   the capacity region." は R1 の結論と同一。⟹ L7 が「同じなら新規性は step 6 + step 10 に限定」と
   書いた退路も、その 2 点が既知だったので**空になった**。

### 殺され方

**最初に壊れるのは step 6 (タイトさ)**。理由は 3 つ:

1. 抽象的な四辺形の形をランダムに振ると `σ = 1` は **1417/2000 で真に緩い** (最大ギャップ
   `5.15`)。緩まないのは `min(S₁,S₂) ≥ A₂` のときだけで、これは最大化点についてしか期待
   できない性質である。⚠ この割合は**実在チャネルの最大化点で緩む頻度ではない** (振っているのは
   形の上位集合)。
2. 部分証明が討ち取れたのは `S₂ ≥ A₂` の側だけで、`S₁ ≥ A₂` 側には現時点で証明も反例も無い。
   `S₁ ≥ A₂ ⟺ I(W;Y) − I(W;Z) ≥ I(U;V|W) − I(U;Y|W)` で、`I(W;Y) < I(W;Z)` (= `W` が受信者 2 に
   偏る) のとき左辺は負になりうる。
3. 最も自然な救済策 (`V' = (V,W)`, `W' = 定数` と吸収する) を実際に代数で試したが、
   `I(U;W|Y) = 0` を要求してしまい**一般には閉じない** — 「明らかに吸収できる」で済ませられない。

**2 番目に壊れるのは (H1) の読み (step 7)** — **L8 の実測: 壊れなかった**。
Conjecture 1 の文そのものは確かに `(α, λ)` を量化していない (記法 `F(T,{a_x})` がパラメータを
落としている) が、**弱い読み「各チャネル対につきある `(α,λ)` でのみ成立」は文献の読みではない**。
決定的な逐語は [N20] — 同じ対象を `F₁^{(λ,α)}` とパラメータを上付きで書き、"For λ ≥ 1 and
α ∈ [0,1], define the following" と量化したうえで加法性を "`F₁₂^{(λ,α)}(η, ζ) = F₁^{(λ,α)}(η) +
F₂^{(λ,α)}(ζ)  ∀η, ζ`" と述べ、Definition 1.4 で "global tensorization property" と名付けている
(`∀` が明示的に付くのは `η, ζ` = `{a_x}` の側だけで、`(λ,α)` は環境変数として全域に量化される)。
補強 2 本: [GLN25] 自身が `min_{α∈[0,1]}` の**内側で** Conjecture 1 を適用している / [AGN19] の
Remark 8 が「(21) のインスタンスが 1 つも無ければ (20) が従う」と述べ、(20) は `min_λ` を外に
持つので (21) は全 `λ` で要る。**⟹ step 9→10 は (H1) の読みでは死なない** (facts §L8 (i))。

**3 番目は step 12 (`M(T)` の閉凸性)** — **L8 の実測: 文献の側では開いていない**。
[AGN19] §I-B が逐語 "Since Marton's achievable region is a convex set in R³₊ …" と主張している
(証明は付かない)。⚠ facts V5 が確定させたのは我々の 2 補助版についてであって対象が違うので、
**我々の Lean `def` の凸性は依然として未証明**。

**⟹ L8 後の総括: R1 は数学的にはどこも壊れなかった。壊れたのは新規性の側である。**
step 1–12 のすべてに逐語出典が付いた ⟹ R1 は正しいが既知の再構成で、経路には昇格しない
(facts §L8 (iv))。**軸 E で残っている未解決は (H1) = Conjecture 1 ただ 1 本**。

**壊れない場所** (念のため): step 2 / 3 / 4 の代数は係数相殺で証明済なので、ここが偽になることは
ない。壊れるとすれば「その代数が `F` の実際の定義に対応していない」= 転記の問題で、**これは L8 の
P1 で実際に 1 件見つかった** — [GLN25] の `F` の第 2 項は `−(λ−α)H(Z)` であって facts V7 が転記した
`−(1−α)H(Z)` ではない (L1 (b) ④ の訂正が正しかった)。R1 の代数はすべて `(λ−α)` 側で組んであるので
経路は無傷。

---

## 付録 — 骨格の訂正 (L7 のブリーフが与えた見立てとの差分)

ブリーフの出発点として与えられた骨格を検算した結果、**2 点が通り、1 点が誤り、1 点が要修正**だった。

| 骨格の主張 | 判定 | 中身 |
|---|---|---|
| `{a_x}` は入力周辺 `p(x)` の双対変数で、`F(T,{a}) = max_p[G_T(p) + ⟨a,p⟩]`、`conc(G_T)(p) = min_a[F − ⟨a,p⟩]` | **通った** | step 4。Fenchel 双対の形は骨格のとおり |
| 共通補助 `W` はこの上凹包を実現する変数 | **通った** | step 3。しかも `α` が `min{I(W;Y), I(W;Z)}` の凸結合の重みであることまで**導出できた** (facts §L5 の 2 行目が「我々の再構成であって逐語ではない」と留保していた点)。**L8 で逐語確認済** — [AGN19] Remark 1 が "It is useful to note that the random variable W plays the role of mixing between various distributions of p(u, v, x), to achieve the concave envelope." と述べ、`α` (= [AGN19] の `λ`) が `min{I(W;Y), I(W;Z)}` を分ける乗数であることは式 (2) の第 3 行に現れる ⟹ **留保は解除された。ただし同時に既知でもある** |
| `G_T(p) := max{(W を持たない目的値) : 入力周辺が p}` | **要修正** | 上凹包を取る対象は `W` を持たない Marton 目的値**そのものではない**。エントロピー項 `−α·H(Y_q) − (μ−α)·H(Z_q)` を**含んだ** `G_{α,μ}` を凹化しないと `F` と合わない (step 3)。素の Marton 目的値を凹化するのは別の対象。**L8 が原文で確認** — [AGN19] の `t_λ(X)` は逐語で `−(δ₁+λ(δ₀+γ₂))I(X;Y) − (1−λ)(δ₀+γ₂)I(X;Z) + max_{p(u,v\|x)}{…}` と、受信者側の情報量項を**含んだ**形で定義されている (`H` 形と `I` 形の差は `p(x)` について線形ゆえ `{a_x}` に吸収される) |
| 「`{a_x}` ↔ `θ` の Legendre」は 2 つの双対化の合成として書く必要がある | **誤り (as framed)** | **`{a_x}` と `θ` の間に Legendre 変換は存在しない**。`θ` は `F` の**内部パラメータ `(α, μ)` として現れる** (step 2: `μ` が方向そのもの、`α` が総和レート乗数の配分) のであって、`a` と共役な関係には無い。正しい絵は `min_α max_p min_a` の **3 段入れ子**で、`a` は最内層、`θ` は最外層の**パラメータ**である。⟹ attack slug `support-vs-dual-additivity` の説明文「`{a_x}` ↔ `θ` の Legendre / 上凹包の段」は**表現として誤解を招く** — 台帳側の文言を「`F` の内部パラメータ `(α,λ)` と方向 `θ` の対応 + 上凹包の段」に直すのが正しい |

**この訂正が実質的である理由**: 「2 つの双対化の合成」という見立てのままだと、`θ` 側にも
Fenchel 変換を探しにいくことになり、存在しないものを探す leg を 1 つ溶かす。実際に必要なのは
**線形計画双対 (step 1) → パラメータ同定 (step 2) → 上凹包 (step 3) → Fenchel (step 4) →
ミニマックス交換 (step 5)** という別種の 5 段で、Legendre 変換が現れるのは step 4 の 1 箇所だけである。

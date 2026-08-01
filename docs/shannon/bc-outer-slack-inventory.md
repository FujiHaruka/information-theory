# BC 外界の緩み inventory — Gohari–Nair Theorem 7 の改善項 ↔ 我々の不等号ステップ

**何の inventory か**: `bc_capacity_subset_uv` (UV 外界の機械検証済 converse) の前方閉包にある**不等号ステップ
全数**に等号成立条件を書き、Gohari–Nair の auxiliary-receiver 外界 (Theorem 7) が「UV 導出で捨てられる項」
として拾い直しているものと対応付けた表。
**親**: [`bc-open-problem-plan.md`](bc-open-problem-plan.md) §4 軸 B `outer-slack-vs-thm7`。
**作成**: L6 (2026-08-02)。**順序は Phase 1 (文献) → Phase 2 (我々) → Phase 3 (対応) を厳守** (逆順は既知の
再発見になる — 親 plan §5-7 novelty gate)。

---

## 0. 再検証コマンド

```bash
# Phase 2 の母集団 (前方閉包)
./scripts/dep_graph.sh InformationTheory.Shannon.BroadcastChannel.bc_capacity_subset_uv
#   -> dep_graph.dot (nodes 1688 / 内部 276 / 外部 1412、edges 16656)
# 内部ノードの抽出 (⚠ macOS の既定 locale の sort は ₁/₂ を同一視するので LC_ALL=C 必須)
rg '\[label' dep_graph.dot | rg -v 'shape=note, style=dashed' \
  | sed 's/^ *"//; s/" \[label.*//' | LC_ALL=C sort -u   # -> 276 行
# 結論形が LE.le のものだけを抽出するには 276 本を #check して結論の head symbol を見る
# (名前フィルタでは不足する — §2.1 参照)
# 根の健全性
#   #print axioms InformationTheory.Shannon.BroadcastChannel.bc_capacity_subset_uv
```

---

## Phase 1 — Theorem 7 の改善項 (逐語)

### 1.1 出典と取得状況

| 項目 | 内容 |
|---|---|
| 出典 | Amin Gohari, Chandra Nair, *Outer bounds for multiuser settings: the auxiliary receiver approach*, IEEE Trans. IT **68**(2):701–736, 2022 |
| PDF | `http://chandra.ie.cuhk.edu.hk/pub/papers/NIT/Auxiliary-Receiver.pdf` (2026-08-02 取得、874,867 bytes) |
| 抽出 | `pdftotext -layout` |

**取得できた箇所**: Abstract / §1 Introduction (p.1–2) / §4 冒頭の Marton 内界 (p.16) / Theorem 6 = UV 外界
(p.16–17) / §4.1 + Theorem 7 + その証明 (p.17–19) / Remark 12 + Corollary 3 (p.19–20) / §4.2 Erasure
Blackwell (p.20–21) / Theorem 8 + **Remark 16** (p.24) / Appendix A の **Lemma 5** とその証明 (p.28–29)。

**取得できなかった箇所**:

- 式 (37) の証明。本文は `The proof for (37) can be found at [EK12, p.226] in the proof of the UV outer
  bound for a general broadcast channel.` とだけ書き、**捨てられる項を本文に書いていない**。⟹ (37) 経路で
  何が落ちるかは本論文からは**取得できず**。
- 論文は「捨てられる項」を**箇条書きのリストとしては提示していない**。名指しで式の形で出てくるのは
  Lemma 5 の (36) の証明中の 1 本のみ (§1.4 の D1)。他は「拾い直した後の形」(Theorem 7 の差分項) からの
  逆算になる。この区別は §1.4 / §1.5 で明示する。
- PDF 抽出時に `ε` (erasure probability) の字が落ちる (`erasure probability ` のように空になる)。逐語引用中
  の該当箇所は `[eps]` と補記した。数式番号・変数名には影響なし。

### 1.2 論文が「捨てられる項を考慮する」と言っている逐語 (p.2)

> In this bound, new auxiliary random variables (defined using past and/or future of the auxiliary
> receiver symbols) are used to minimize the discarded terms in the various routine manipulations. In
> particular, the UV outer bound (a previously known outer bound on the capacity of a general broadcast
> channel) and the terms that are discarded in its derivation are considered. The bound is modified to
> minimize the discarded terms using the new auxiliary random variables. This then led to a (strict)
> tightening of the rate constraints, whose strictness is then demonstrated using a concrete example.

Abstract 相当の動機 (p.2):

> Suppose one erases the output of every receiver with probability [eps], then the traditional
> single-letter outer bounds scale by (1 − [eps]); however the achievable region does not (see Section
> 4.1). This motivated the authors, thanks also to a question asked by Young-Han Kim, to investigate
> whether the true capacity region also scaled by (1 − [eps]). It was here that the auxiliary receiver
> idea originated as a tool to show that the true capacity region did not have the (1 − [eps]) scaling
> property, as the outputs of the auxiliary channels need not undergo any erasure.

### 1.3 ベースライン — Theorem 6 (UV 外界) 逐語 (p.16–17)

> **Theorem 6 (UV outer bound).** Any achievable rate `(R0, R1, R2)` satisfies the constraints
> `R0 ≤ min(I(W;Y), I(W;Z))`,
> `R0 + R1 ≤ min(I(W;Y), I(W;Z)) + I(U;Y|W)`,
> `R0 + R2 ≤ min(I(W;Y), I(W;Z)) + I(V;Z|W)`,
> `R0 + R1 + R2 ≤ min(I(W;Y), I(W;Z)) + min(I(U;Y|W) + I(X;Z|U,W), I(V;Z|W) + I(X;Y|V,W))`,
> for some triple of random variables `(U, V, W)` such that `(U,V,W) −− X −− (Y,Z)`.

**我々の領域との差**: 我々の `bcOuterRegionUV` は `R₀ = 0` / `W = const` の射影 (共通メッセージなし)。
その場合 `min(I(W;Y),I(W;Z)) = 0` となり、上の 4 本は我々の `InBCOuterRegionUV` の 4 本
(`bound₁ : R₁ ≤ I₁`, `bound₂ : R₂ ≤ I₂`, `sumBound₂`, `sumBound₁`) と一致する
(`uvInfo₁ = I(V;Y₁)`, `uvInfo₂ = I(U;Y₂)`, `uvInfoSum₁ = I(V;Y₁) + I(X;Y₂|V)`,
`uvInfoSum₂ = I(U;Y₂) + I(X;Y₁|U)`; 論文の `min` を 2 本の制約に割った形)。

### 1.4 名指しで書かれている「捨てられる項」

**D1 — Lemma 5 の (36) の証明中に現れる唯一の逐語の捨て項** (p.29)。論文は (36)

> `I(U;Bⁿ|V) + I(U;Aⁿ|V) − I(U;Bⁿ|V) ≤ Σᵢ [ I(U,B^n_{i+1};Bᵢ|V) + I(U,B^n_{i+1},A^{i-1};Aᵢ|V) −
> I(U,B^n_{i+1},A^{i-1};Bᵢ|V) ]`

を導くとき、等式変形の最後に

> `− I(A^{i-1}; Aᵢ|V)`

という項が残り、それを非負性で落として `≤` にしている。**これが UV 単一文字化で捨てられる項の逐語**。
論文の証明の該当行は `= Σᵢ [ … − I(A^{i-1}; Aᵢ|V) ]` (Lemma 5 の証明、(36) の導出末尾)。

補足 (Lemma 5 の位置づけ、p.28 Remark 18): 論文は Csiszár sum lemma を **Körner–Márton Lemma** と改称し、
`Lemma 5` はその「converse で使う汎用操作」をまとめたもの。Theorem 7 の証明は
`They are then single-letterized using Lemma 5, guided by the identifications mentioned above.` と書く。
⟹ **UV 導出で項が落ちる箇所は Lemma 5 の各不等式に局在している**。

**D2 — 式 (37) 経路の捨て項: 取得できず** (§1.1)。(37) は
`I(U;Aⁿ|V) + I(V;Bⁿ) ≤ Σᵢ [ I(U;Aᵢ|V,A^n_{i+1},B^{i-1}) + I(V,A^n_{i+1},B^{i-1};Bᵢ) ]`。

**D3 — 補助変数の同定そのもの (「落とす」ではなく「太らせる」型の緩み)**。Theorem 7 の証明の同定 (p.18):

> `Ŵ = (M0, J^{Q-1}, Y^n_{Q+1}, Q)`, `W̃ = (M0, Z^{Q-1}, J^n_{Q+1}, Q)`,
> `W = (M0, Z^{Q-1}, Y^n_{Q+1}, Q)`, `U = Û = Ũ = M1`, `V = V̂ = Ṽ = M2`.

UV では `W = (M0, Z^{Q-1}, Y^n_{Q+1}, Q)` の 1 種類しか使わない。Theorem 7 は同じ n-letter 量を
`Ŵ`/`W̃` の 2 系統でも読み、両者の差を (19)(20) で縛る。

### 1.5 Theorem 7 の拾い直し機構 (3–8 行)

Theorem 7 (p.17–18) は任意の補助チャネル `T_{J|X,Y,Z}` に対し (18a)–(18i) を課す。拾い直しの機構は 3 つ:

1. **差分化**: UV が捨てていた量を `I(Ŵ;Y) − I(Ŵ;J)` / `I(W̃;Z) − I(W̃;J)` / `I(Û;Y|Ŵ) − I(Û;J|Ŵ)` /
   `I(Ṽ;Z|W̃) − I(Ṽ;J|W̃)` という**補助受信者への流量との差**に置き換える。落とす代わりに J への流量を
   足して引く。
2. **差の分割を等式で縛る**: (19a) `I(W̃;Z) − I(W̃;J) + I(Ŵ;J) − I(Ŵ;Y) = I(W;Z) − I(W;Y)`、(19b)(19c) が
   `U`/`V` 側の同型。UV では自由だった 2 系統の差の配分が、ここで 1 自由度に縛られる。
3. **落としていた入力項を挟み込みで残す**: (20a) `0 ≤ I(X;Z|Ũ,W̃) − I(X;J|Ũ,W̃) ≤ I(Ṽ;Z|W̃) − I(Ṽ;J|W̃)`、
   (20b) が鏡像、(20c) `I(V;Z|W) + I(X;Y|V,W) = I(U;Y|W) + I(X;Z|U,W)` は UV が `min` で潰していた 2 式を
   **等号**で結ぶ。

**Remark 12 (p.19) 逐語** — Theorem 7 ⊇ UV であることの確認:

> **Remark 12.** From (18a), (18b), (18e), (18i), we can extract the following constraints:
> `R0 ≤ min{I(W;Y), I(W;Z)}`,
> `R0 + R1 ≤ min{I(W;Y), I(W;Z)} + I(U;Y|W)`,
> `R0 + R2 ≤ min{I(W;Y), I(W;Z)} + I(V;Z|W)`,
> `R0 + R1 + R2 ≤ min{I(W;Y), I(W;Z) + min{I(U;Y|W) + I(X;Z|U,W), I(V;Z|W) + I(X;Y|V,W)}`.
> This implies that the outer bound in Theorem 7 is at least as good as the UV outer bound for all
> broadcast channels `T(y,z|x)`.

**Remark 16 (p.24) 逐語** — Lemma 5 を経由しない別ルートで、UV の各不等式を「そのまま形式的に置換する」
だけで J-bound が出ることを示す箇所 (どこが緩みの本体かの直接の証拠):

> **Remark 16.** An alternative approach to single-letterize (33a)-(33g) that skips using Lemma 5 is as
> follows: consider the UV bound in Theorem 6. Take for instance, the sum-rate constraint:
> `R0 + R1 + R2 ≤ I(W;Y) + I(U;Y|W) + I(X;Z|U,W)`. This inequality is shown via the following expansion
> `I(M0;Yⁿ) + I(M1;Yⁿ|M0) + I(M2;Zⁿ|M0,M1) ≤ Σᵢ (I(Wᵢ;Yᵢ) + I(Uᵢ;Yᵢ|Wᵢ) + I(Xᵢ;Zᵢ|Uᵢ,Wᵢ))`, (34)
> where `Wᵢ = (M0, Y^{i-1}, Z^n_{i+1})` and `Uᵢ = M1`. The inequality (34) holds for any arbitrary joint
> distribution of `p_{M0,M1,M2,Yⁿ,Zⁿ}`. Thus, it continues to hold if we formally replace `M0` and `Zⁿ`
> by `M̃0 = (M0, Jⁿ)` and `Ĵⁿ` respectively, while keeping all the other variables intact.

**⟹ Phase 3 で使う 3 つの「捨てられる項」**: **D1** (`I(A^{i-1};Aᵢ|V)` — 逐語)、**D2** (取得できず)、
**D3** (補助変数同定の一意性 = Ŵ/W̃ を使わないこと。逐語の「捨て項」ではなく Theorem 7 の構造からの逆算)。

---

## Phase 2 — 我々の不等号ステップ

### 2.1 規模の再導出 — 21 ではなく **39**

L4 の「21 本」は `dep_graph.sh` + **名前フィルタ**の結果で、結論形での全数ではない。今回は 276 本の内部
decl を実際に elaborate し、`∀` を剥がした結論の head symbol で分類した:

| 結論 head | 本数 |
|---|---|
| `Eq` | 101 |
| **`LE.le`** | **39** |
| `MeasurableSet` | 12 |
| `Membership.mem` | 8 |
| `IsMarkovChain` | 9 |
| `IsProbabilityMeasure` | 6 |
| `IsUVChannelLaw` | 6 |
| その他 (`EventuallyEq` / `IsMarkovKernel` / `InBCOuterRegionUV` / `Iff` / `False` / `And` / …) | 95 |

⚠ **落とし穴 2 件** (再現時の注意):

1. macOS の既定 locale の `sort -u` は `₁` (U+2081) と `₂` (U+2082) を**同一視して潰す**。276 → 251 に
   縮み、`bcConverseFanoSlack₂_le` / `bcUVTimeShare_uvInfo₂_ge` / `bc_uv_singleletterize_sum₂` などの
   ₂-側が丸ごと消える。`LC_ALL=C sort` が必須。
2. 結論の head を取るとき `whnf` をかけると `LE.le` がインスタンス経由で展開されて 0 件になる。
   `forallTelescopeReducing` の本体をそのまま `getAppFn.constName?` で読むこと。

**根の健全性**: `bc_capacity_subset_uv` は `[propext, Classical.choice, Quot.sound]` のみに依存
(2026-08-02 実測、再検証は §0 のコマンド)。⟹ 以下の 39 本はすべて機械検証済の連鎖の一部。

### 2.2 39 本の表

**分類**: `主鎖-P` = rate 制約を形作り、緩みが n→∞ で残りうる / `主鎖-V` = rate 制約を形作るが緩みが
消える (Fano 系、論文の `+ n·g(εₙ)` に対応) / `道具` = DPI 系の汎用不等式 / `補助` = 可測性・正則性・
算術の配管 (情報論的な緩みを持たない)。

| # | decl | file:line | 等号成立条件 | 区分 |
|---|---|---|---|---|
| 1 | `uvAux_absorbs_receiver1_terms` | `InformationTheory/Shannon/BroadcastChannel/OuterBoundUV.lean:407` | 捨て項は `I(Y₁^{<i}; Y₁ᵢ)`。等号 ⟺ 受信者 1 の出力の過去が現出力と独立 | 主鎖-P |
| 2 | `uvAux_absorbs_receiver2_terms` | 同 `:340` | 捨て項は `I(Y₂^{>i}; Y₂ᵢ)`。等号 ⟺ 受信者 2 の出力の未来が現出力と独立 | 主鎖-P |
| 3 | `bc_uv_singleletterize_r1` | 同 `:113` | 捨て項は各 i で `I(Y₁^{<i};Y₁ᵢ) + I(Y₂^{>i};Y₁ᵢ \| W₁,Y₁^{<i})`。等号 ⟺ 両方 0 | 主鎖-P |
| 4 | `bc_uv_singleletterize_r2` | 同 `:174` | 3 の鏡像 (`Y₂` 側) | 主鎖-P |
| 5 | `bc_uv_singleletterize_sum₁` | 同 `:684` | 3 と同じ捨て項 + Csiszár sum の telescoping (等式)。等号 ⟺ 3 の条件 | 主鎖-P |
| 6 | `bc_uv_singleletterize_sum₂` | 同 `:637` | 5 の鏡像 | 主鎖-P |
| 7 | `bc_uv_input_step` | 同 `:519` | `I(Xⁿ;Y₁ᵢ\|W,Y₁^{<i}) ≤ I(Y₂^{>i};Y₁ᵢ\|W,Y₁^{<i}) + I(Xᵢ;Y₁ᵢ\|uvAuxᵢ)`。捨て項 `I(Y₂^{>i};Y₁ᵢ\|W,Y₁^{<i},Xⁿ)` は仮説 `h_memo` (memoryless) の下で **0** ⟹ **常に等号** (手計算、未機械検証) | 主鎖-P |
| 8 | `bc_uv_input_step'` | 同 `:570` | 7 の鏡像。同じく 0 | 主鎖-P |
| 9 | `condMutualInfo_le_add_condMutualInfo` | `.../OuterBoundUV/Gateway.lean:194` | `I(A;C\|Z) ≤ I(B;C\|Z) + I(A;C\|Z,B)`。捨て項は `I(B;C\|Z,A)`。等号 ⟺ `B −− (Z,A) −− C` | 主鎖-P |
| 10 | `mutualInfo_le_condMutualInfo_of_indep_markov` | `.../OuterBoundUV.lean:760` | `I(W₁;Yⁿ) ≤ I(Xⁿ;Yⁿ\|W₂)`。捨て項は (a) `I(W₁;W₂\|Yⁿ)` (メッセージ独立性を条件付きに移す代償) + (b) `I(Xⁿ;Yⁿ\|W₁,W₂)` (決定的符号器なら 0)。等号 ⟺ 両方 0 | 主鎖-P |
| 11 | `bcUVTimeShare_uvInfo₁_ge` | `.../OuterBoundUV/Assembly.lean:324` | 証明末が `le_add_self`。捨て項は時分割指標との相互情報 `I(Q;Y₁)`。等号 ⟺ `Y₁` の周辺分布が letter 位置に依存しない | 主鎖-P |
| 12 | `bcUVTimeShare_uvInfo₂_ge` | 同 `:342` | 11 の鏡像 (`I(Q;Y₂)`) | 主鎖-P |
| 13 | `bcUVTimeShare_uvInfoSum₁_ge` | 同 `:427` | 11 と同じ (`uvInfoSum₁` の conditional 部分は `bcUVTimeShare_condMutualInfo₁_eq` で**等式**、緩みは `uvInfo₁` 側の `I(Q;Y₁)` のみ) | 主鎖-P |
| 14 | `bcUVTimeShare_uvInfoSum₂_ge` | 同 `:419` | 13 の鏡像 | 主鎖-P |
| 15 | `bcConverseFanoSlack₁_le` | 同 `:509` | Fano slack `≤ log 2 + Pe·log M₁`。等号 ⟺ `binEntropy(Pe) = log 2` すなわち `Pe = 1/2`、かつ `log(M₁−1) = log M₁` (M₁→∞ 極限) | 主鎖-V |
| 16 | `bcConverseFanoSlack₂_le` | 同 `:524` | 15 の鏡像 | 主鎖-V |
| 17 | `shannon_converse_single_shot` | `InformationTheory/Shannon/Converse.lean:70` | Fano + DPI の合成。等号 ⟺ 18 の等号条件 かつ DPI が tight | 主鎖-V |
| 18 | `fano_inequality_measure_theoretic` | `InformationTheory/Fano/Measure.lean:262` | 古典 Fano。等号 ⟺ 誤り時の条件付き分布が誤答 `M−1` 点上で一様、かつ誤り事象が `Y` と独立 | 主鎖-V |
| 19 | `pointwise_fano` | 同 `:213` | 18 の点ごと版 (`fano_core` の特殊化)。等号条件は 20 に同じ | 主鎖-V |
| 20 | `fano_core` | `InformationTheory/Fano/Core.lean:379` | `H(X\|Y) ≤ H_q(Pe)`。等号 ⟺ 誤り指示子の条件付き分布が `Y` に依存せず、誤答が一様 | 主鎖-V |
| 21 | `withErr_condE_Y_le_binEntropy_errorProb` | 同 `:239` | Jensen (binEntropy の凹性)。等号 ⟺ 誤り確率が `xh` によらず一定 | 主鎖-V |
| 22 | `withErr_condX_EY_le` | 同 `:297` | 誤答上の一様上界。等号 ⟺ 誤答が `M−1` 点上で一様 | 主鎖-V |
| 23 | `sum_negMulLog_sub_le_sum_mul_log_card` | 同 `:84` | 台 `S` 上のエントロピー上界。等号 ⟺ `μ` が `S` 上一様 | 主鎖-V |
| 24 | `entropyOfFn_le_log_supportCard` | `InformationTheory/Fano/Entropy.lean:41` | 等号 ⟺ `μ` が `S` 上一様 | 主鎖-V |
| 25 | `binEntropy_jensen_finset` | `InformationTheory/Fano/BinaryJensen.lean:28` | Jensen。等号 ⟺ `p i` が重み正の `i` 上で定数 (binEntropy は狭義凹) | 主鎖-V |
| 26 | `integral_qaryEntropy_le_qaryEntropy_integral` | `InformationTheory/Fano/Measure.lean:228` | Jensen (積分版)。等号 ⟺ `g` が `ν`-a.e. 定数 | 主鎖-V |
| 27 | `klDiv_map_le` | `InformationTheory/Shannon/DPI.lean:43` | DPI (KL)。等号 ⟺ `f` が `{μ,ν}` の十分統計量 (尤度比が `σ(f)`-可測) | 道具 |
| 28 | `mutualInfo_le_of_postprocess` | 同 `:123` | `I(X;f(Y)) ≤ I(X;Y)`。等号 ⟺ `X −− f(Y) −− Y` が Markov | 道具 |
| 29 | `mutualInfo_le_of_markov` | `InformationTheory/Shannon/CondMutualInfo.lean:366` | `X−−Z−−Y` の下で `I(X;Y) ≤ I(Z;Y)`。等号 ⟺ さらに `Z−−X−−Y` (`I(Z;Y\|X)=0`)、すなわち `X` も十分統計量 | 道具 |
| 30 | `condMutualInfo_le_of_markov_joint` | `.../ConverseMemorylessChainRule.lean:113` | 条件付き DPI。等号 ⟺ `I(Z;Y\|X,W)=0` | 道具 |
| 31 | `withErr_nonneg` | `InformationTheory/Fano/Core.lean:221` | 等号 ⟺ 質量 0 | 補助 |
| 32 | `marginalEY_nonneg` | `InformationTheory/Fano/CondEntropy.lean:71` | 等号 ⟺ 質量 0 | 補助 |
| 33 | `marginalY_nonneg` | 同 `:77` | 等号 ⟺ 質量 0 | 補助 |
| 34 | `averageErrorProb₁_le_one` | `.../BroadcastChannel/OuterBound.lean:137` | 等号 ⟺ 全メッセージで復号失敗 | 補助 |
| 35 | `averageErrorProb₂_le_one` | 同 `:154` | 同上 | 補助 |
| 36 | `errorProbAt₁_le_one` | `.../BroadcastChannel/Basic.lean:116` | 確率 ≤ 1。等号 ⟺ 確率 1 | 補助 |
| 37 | `errorProbAt₂_le_one` | 同 `:125` | 同上 | 補助 |
| 38 | `le_log_of_ceil_exp_le` | `.../ChannelCoding/CodeToAmbient.lean:690` | `x ≤ log M`。等号 ⟺ `exp x` が整数で `M = ⌈exp x⌉` | 補助 |
| 39 | `le_toReal_of_inv_mul_le` | 同 `:700` | `ℝ≥0∞` 配管。等号 ⟺ 入力の 2 不等式がともに等号 | 補助 |

**内訳**: 主鎖-P 14 / 主鎖-V 12 / 道具 4 / 補助 9 = 39。

---

## Phase 3 — 対応表

**判定語**: `matched` = Theorem 7 (または論文の `+ n·g(εₙ)`) が同じ項を拾い直している / `no-slack` =
使用時の仮説の下で捨て項が 0 (緩みが存在しない) / `unmatched` = 対応が付かない。
`unmatched` の理由は **(i) 我々固有の緩み / (ii) 証明の構成が違うだけ / (iii) 論文の記述から読み取れない**
の 3 択で明示する。

| # | 我々のステップ | 捨てられる項 | Theorem 7 の対応 | 判定 |
|---|---|---|---|---|
| 1 | `uvAux_absorbs_receiver1_terms` | `I(Y₁^{<i}; Y₁ᵢ)` | **D1 逐語一致**: Lemma 5 (36) の証明で落ちる `I(A^{i-1};Aᵢ\|V)` に `A := Y₁`, `V := ∅` を代入した形 | `matched` |
| 2 | `uvAux_absorbs_receiver2_terms` | `I(Y₂^{>i}; Y₂ᵢ)` | D1 の時間反転版 (Lemma 5 の (35) の第 2 表示に対応) | `matched` |
| 3 | `bc_uv_singleletterize_r1` | `I(Y₁^{<i};Y₁ᵢ)` + `I(Y₂^{>i};Y₁ᵢ\|W₁,Y₁^{<i})` | 第 1 項 = D1。第 2 項 = **D3**: 補助変数を `uvAuxᵢ = (W₁, Y₁^{<i}, Y₂^{>i})` に太らせて吸収する操作そのもの — Theorem 7 が `Ŵ = (M0,J^{Q-1},Y^n_{Q+1},Q)` / `W̃ = (M0,Z^{Q-1},J^n_{Q+1},Q)` に差し替える対象 | `matched` |
| 4 | `bc_uv_singleletterize_r2` | 3 の鏡像 | 同上 | `matched` |
| 5 | `bc_uv_singleletterize_sum₁` | 3 と同じ | 論文 (34) (Remark 16 逐語) と同じ展開。Theorem 7 は `M0 → (M0,Jⁿ)`, `Zⁿ → Ĵⁿ` の形式的置換でここを強化 | `matched` |
| 6 | `bc_uv_singleletterize_sum₂` | 5 の鏡像 | 同上 | `matched` |
| 7 | `bc_uv_input_step` | `I(Y₂^{>i};Y₁ᵢ\|W,Y₁^{<i},Xⁿ)` = 0 (h_memo の下) | 論文の「routine manipulation」の 1 段だが緩みを持たない | `no-slack` |
| 8 | `bc_uv_input_step'` | 同上 = 0 | 同上 | `no-slack` |
| 9 | `condMutualInfo_le_add_condMutualInfo` | `I(B;C\|Z,A)` (抽象形)。7/8 での適用時は 0 | 7/8 の汎用版。抽象形のままでは論文に対応物なし、適用時は緩みなし | `no-slack` |
| 10 | `mutualInfo_le_condMutualInfo_of_indep_markov` | `I(W₁;W₂\|Y₂ⁿ)` (+ 決定的符号器なら 0 の `I(Xⁿ;Yⁿ\|W₁,W₂)`) | **対応なし**。論文は Fano を `(M0,M1)` 条件付きで適用し `nR₂ ≤ I(M₂;Zⁿ\|M0,M1) + n·g(εₙ)` を**等式的に**得るため、この項を作らない | `unmatched` **(i)** |
| 11 | `bcUVTimeShare_uvInfo₁_ge` | `I(Q;Y₁)` (証明末 `le_add_self`) | **対応なし**。論文は `Q` を補助変数 `Ŵ`/`W̃`/`W` の成分として最初から埋め込むので、時分割は不等式として現れない | `unmatched` **(ii)** |
| 12 | `bcUVTimeShare_uvInfo₂_ge` | `I(Q;Y₂)` | 同上 | `unmatched` **(ii)** |
| 13 | `bcUVTimeShare_uvInfoSum₁_ge` | `I(Q;Y₁)` | 同上 | `unmatched` **(ii)** |
| 14 | `bcUVTimeShare_uvInfoSum₂_ge` | `I(Q;Y₂)` | 同上 | `unmatched` **(ii)** |
| 15–16 | `bcConverseFanoSlack₁/₂_le` | Fano slack | 論文 (21a)–(21i) の `+ n·g(εₙ)`。`εₙ → 0` で消える | `matched` |
| 17–26 | `shannon_converse_single_shot`, `fano_inequality_measure_theoretic`, `pointwise_fano`, `fano_core`, `withErr_condE_Y_le_binEntropy_errorProb`, `withErr_condX_EY_le`, `sum_negMulLog_sub_le_sum_mul_log_card`, `entropyOfFn_le_log_supportCard`, `binEntropy_jensen_finset`, `integral_qaryEntropy_le_qaryEntropy_integral` | Fano 内部の Jensen / 一様上界 | 同じく `+ n·g(εₙ)` に吸収。論文は Fano を補題として引くだけで内部を展開しない | `matched` |
| 27–30 | `klDiv_map_le`, `mutualInfo_le_of_postprocess`, `mutualInfo_le_of_markov`, `condMutualInfo_le_of_markov_joint` | DPI の緩み | Theorem 7 が J を差し込む場所そのもの。Corollary 3 の証明 (p.19) が逐語で `From (18c), since I(Û;Ŷ\|Ŵ) ≥ I(Û;Y\|Ŵ), we see that …` と、まさに DPI の緩みを `J = Ŷ` で回収している | `matched` |
| 31–39 | `withErr_nonneg`, `marginalEY_nonneg`, `marginalY_nonneg`, `averageErrorProb₁/₂_le_one`, `errorProbAt₁/₂_le_one`, `le_log_of_ceil_exp_le`, `le_toReal_of_inv_mul_le` | なし (情報論的な緩みを持たない配管) | 対応なし・対応不要 | `no-slack` |

**集計**: `matched` 22 / `no-slack` 12 (7,8,9 + 補助 9) / `unmatched` 5 / `未判定` 0。

---

## 判定

### `unmatched` 5 本とその理由

| 本数 | 理由 | 中身 |
|---|---|---|
| 1 | **(i) 我々固有の緩み** | `mutualInfo_le_condMutualInfo_of_indep_markov` の `I(W₁;W₂\|Y₂ⁿ)`。論文は Fano を条件付きで適用してこの項を作らない |
| 4 | **(ii) 構成が違うだけ** | `bcUVTimeShare_*_ge` 4 本の `I(Q;Y₁)` / `I(Q;Y₂)`。論文は `Q` を補助変数に埋め込み済 |
| 0 | (iii) 論文から読み取れない | なし (D2 = (37) の捨て項は取得できなかったが、我々の側に対応する未分類ステップは残らなかった) |

### `unmatched` は新しい標的になるか — **ならない**

5 本とも**最終領域を動かさない**。理由:

- **(ii) の 4 本**: `I(V;Y₁) = I(Q;Y₁) + I(V;Y₁|Q)` で、`Q` は `V` の第 1 成分。落とした `I(Q;Y₁)` を残して
  `R₁ ≤ I(V;Y₁|Q)` に締めても、`bcOuterRegionUV` は**すべての UV 法 `ν` の合併**なので、独立な `Q` を持つ
  `ν` を取れば `I(Q;Y₁) = 0` で同じ点が入る。合併は縮まない。
- **(i) の 1 本**: 同じ理由に加え、`bc_uv_converse` の結論は論文の Theorem 6 と同一の領域である
  (§1.3 で照合済)。**証明内部の緩みは、結論が同じ領域に着地している限り、より強い外界を生まない**。

⟹ 軸 B の第一標的 (i) 「我々の Lean 証明のどのステップが Theorem 7 の改善項に対応するか」は**同定が完了し、
同時にその同定が「我々固有の exploitable な緩みは 0 本」を意味する**。exploitable な緩み (D1 と D3) は
すべて論文が既に回収済み。

### 親 plan §3.1 の (1)(2) の形で次の一手が書けるか

**(1) 主張が 1 文で書けるか — YES (ただし否定的な形)**:

> `bc_capacity_subset_uv` の前方閉包にある 39 本の不等号ステップのうち、捨て項が最終領域 `bcOuterRegionUV`
> の単一文字変数だけで表せるものは 0 本であり、したがって UV 外界の証明を我々の側で締め直しても
> `bcOuterRegionUV` は真に縮まない。

**(2) ステップが列挙できるか — YES**:

1. 39 本を主鎖-P / 主鎖-V / 道具 / 補助 に分類する (§2.2、`known`: 本 inventory で完了)
2. 主鎖-V 12 本の緩みが `εₙ → 0` で消えることを示す (`known`: 論文の `+ n·g(εₙ)` と同型)
3. 主鎖-P の捨て項を 4 種 (`I(Y₁^{<i};Y₁ᵢ)` / `I(Y₂^{>i};Y₂ᵢ)` / `I(Q;Y·)` / `I(W₁;W₂|Y·ⁿ)`) に還元する
   (`known`: §2.2)
4. 各捨て項について「合併を取ると消える」ことを示す (`new`: 上の 2 つの論証を形式化するなら新規。
   散文レベルでは §判定 に完了)
5. ⟹ 結論 (1) (`new`)

⟹ **(1)(2) は書ける。ただし帰結は否定的**なので、これを「候補経路」として台帳に載せる価値は低い
(親 plan §3.1 の条件 5「既知でない」は満たすが、T2「人類未知の中間結果」ではなく、我々の証明に対する
**診断結果**)。軸 B の収穫ラインは満たされた: **Theorem 7 の改善項 ↔ 我々の証明ステップの対応表**
(§Phase 3) が機械検証済の連鎖に対して残った。

### 残る開いた標的 (軸 B の (ii))

論文自身が Theorem 7 の最適性を主張していない (親 plan F3 の「Li 曰く optimality unknown」)。本 leg で
新たに分かったのは、**その標的に触るには領域の定義を J でパラメタ化する必要がある**ということ:
我々の `bcOuterRegionUV` は `J` を持たないので、現在の在庫のままでは (ii) に 1 行も書けない。
前提工事として `bcOuterRegionJ` (Theorem 7 の (18a)–(18i) + (19)(20) を満たす法の合併) の定義が要る。
これは §1.3 の照合で `InBCOuterRegionUV` が 4 フィールドの `structure` である以上、9 制約 + 3 等式 +
3 挟み込みの `structure` を新設する作業になる (**形式化タスク**であり、本 relay のスコープ外 — 親 plan §2.1)。

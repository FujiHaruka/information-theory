# N11 — `δ ≥ 0` (more capable の不等式) の層 3 化 (判定枠 第 2 組の第 3 段)

**Parent**: [`bc-open-problem-t3c-plan.md`](bc-open-problem-t3c-plan.md) §5.1 (N11 起票ブロック) /
**前段** = [`bc-t3c-n10-epsilon-zero.md`](bc-t3c-n10-epsilon-zero.md) §2.5 + 訂正 5 (⚠ **論法の SoT はそちら。本書は複製しない**)。

**leg 冒頭宣言 (N11)** (⚠ 起票 §5.1 L414 からの逐語コピー): 側 = (C2) / 動かすもの = §0 が要求する Lean 側 (層 3) を、
N10 の判定を支えている唯一の解析的入力 `δ ≥ 0` の分だけ動かし、判定枠 第 2 組が散文で閉じた解析核が機械検証された状態にする

> **着地** = `InformationTheory/Shannon/BroadcastChannel/MoreCapableBinary.lean` (新規 406 行、35 宣言、`sorry` **0**)。
> **標的 1 本 + 半空間版 1 本の計 2 本**が `@[entry_point]` で載り、両方 **sorryAx-free** である。
> ⚠⚠ **落としてはならない限定は §4 に全部書いた** — 載ったのは**実数変数レベルの 1 変数不等式 1 本**であって、
> **レート領域の包含についても [probc] の判定そのものについても 1 文字も言っていない**。

---

## 1. 載ったもの

**ファイル**: `InformationTheory/Shannon/BroadcastChannel/MoreCapableBinary.lean` (新規)。
**配線**: `InformationTheory.lean` L134 に `import` を追記済 (`OuterBoundTransport` の直後)。

### 1.1 標的 (起票 §5.1 L419–L423 の逐語形)

`MoreCapableBinary.lean:379`:

```lean
@[entry_point]
theorem log_two_mul_binEntropy_binConv_sub_binEntropy_le (hp₀ : 0 < p) (hp₁ : p < 1 / 2)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    Real.log 2 * (Real.binEntropy (x * (1 - p) + (1 - x) * p) - Real.binEntropy p)
      ≤ (Real.log 2 - Real.binEntropy p) * Real.binEntropy x
```

⚠ **起票が SoT と名指した式と逐語で一致する** (`x * (1 - p) + (1 - x) * p` を def へ畳まず生の形で置いた —
畳むと「本当に `δ ≥ 0` を載せたのか」の検証に def の展開が 1 段挟まるため)。
仮説は `p` の定義域 (`0 < p < 1/2`) と `x` の定義域 (`0 ≤ x ≤ 1`) の**4 本だけ**であり、
⚠ **解析的な内容を持つ仮説は 1 本も無い** (load-bearing hypothesis 無し)。

### 1.2 半空間版 (起票 §5.1 L425 の「候補」— **置いた**)

`MoreCapableBinary.lean:392`:

```lean
@[entry_point]
theorem binEntropy_binConv_sub_binEntropy_le {e : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1 / 2)
    (he : e * Real.log 2 ≤ Real.binEntropy p) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    Real.binEntropy (x * (1 - p) + (1 - x) * p) - Real.binEntropy p
      ≤ (1 - e) * Real.binEntropy x
```

⚠ **起票の候補式から仮説 `0 ≤ e` を 1 本落とした** — 証明に使わないからである
(効いているのは `e * log 2 ≤ binEntropy p` ⟺ `e ≤ h₂(p)` の 1 本だけ。
これは N10 訂正 4 の「効いている条件は `δ ≥ 0` ⟺ `e ≤ h(p)` の 1 本だけ」と整合する)。
⚠ **落とした側が真に強い**ので起票の候補式は本定理から `0 ≤ e` を足すだけで出る。

### 1.3 `#print axioms` (逐語)

```
'InformationTheory.Shannon.BroadcastChannel.log_two_mul_binEntropy_binConv_sub_binEntropy_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InformationTheory.Shannon.BroadcastChannel.binEntropy_binConv_sub_binEntropy_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

再現手順: 当該ファイル末尾に `#print axioms <full name>` を 2 行足して
`lake env lean InformationTheory/Shannon/BroadcastChannel/MoreCapableBinary.lean`。

### 1.4 `δ` との対応 (⚠ 自前で再導出した。ブリーフの式は信用していない)

`Real.binEntropy` は自然対数系である (`Real.binEntropy_two_inv : binEntropy 2⁻¹ = Real.log 2` を
`Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean:69` で逐語確認)。`L := Real.log 2`、`h₂ := binEntropy / L` として

- `δ(x) = C·h₂(x) − (h₂(x∗p) − h₂(p))`、`C = 1 − h₂(p)` の両辺に `L²` を掛けると
  `L²·δ(x) = (L − binEntropy p)·binEntropy x − L·(binEntropy (x∗p) − binEntropy p)`。

⟹ **標的 = `L²·δ(x) ≥ 0`** であり、`L² > 0` ゆえ `δ ≥ 0` と同値である。
⭐ **独立の数値照合**: `p = 0.1, x = 0.3` で `δ·L² = 0.0058356973454775410`、
Lean の標的の左右差 = `0.0058356973454775085` (一致)。
`p ∈ {0.001,…,0.499} × x ∈ {0,…,1}` の 499×1001 格子で左右差の最小は `-7.7e-17` (= 零点 `x ∈ {0, 1/2, 1}` の丸め)。
⭐ **N10 との独立の突き合わせが 1 本ある** — 本 leg の `inflection p` (変化点の閉形) を `p = 0.1` で評価すると
**`0.198699`** で、N10 §2.5 が報告した変化点 **`x0 = 0.198699324`** と一致する
⟹ **本 leg の `curvatureThreshold` が N10 の `sign δ''` と同じ量を指している**ことの独立確認になっている。
⚠ **この数値照合は証拠ではない** (証拠は Lean 側)。**標的を取り違えていないことの確認**に使っただけである。

---

## 2. 採った証明ルート

**起票の参照ルート (N10 §2.5 + 訂正 5) をそのまま採った**。逸れたのは 1 点だけ (下記 (d))。

`gapFun p x := (L − binEntropy p)·binEntropy x − L·(binEntropy (binConv p x) − binEntropy p)` (`= L²·δ`) を主役に置き:

- **(a) 端点と対称性** — `gapFun p 0 = 0` / `gapFun p 2⁻¹ = 0` / `gapFun p (1−x) = gapFun p x` /
  `gapFunDeriv p 2⁻¹ = 0`。効いた Mathlib 補題: `Real.binEntropy_zero` / `Real.binEntropy_two_inv` /
  `Real.binEntropy_one_sub`。⚠ **`gapFunDeriv p 2⁻¹ = 0` は極値の議論を経ずに、`x = 2⁻¹` で
  `log(1−x) − log x` と `log(1−x∗p) − log(x∗p)` の両方が `0` になるという恒等式から直接出る**。
- **(b) 1 階・2 階微分** — `hasDerivAt_gapFun` / `hasDerivAt_gapFunDeriv` を `(0,1)` 上で明示関数として建てた。
  効いた Mathlib 補題: `Real.hasDerivAt_binEntropy` (`BinaryEntropy.lean:257`) / `HasDerivAt.comp` /
  `HasDerivAt.log` / `HasDerivAt.const_sub` / `HasDerivAt.congr_deriv` / `hasDerivAt_id'`。
  ⚠ **`Real.deriv2_binEntropy` は使っていない** — `deriv^[2]` を経由せず `f'`, `f''` を明示関数として渡す
  `concaveOn_of_hasDerivWithinAt2_nonpos` 系 (`Mathlib/Analysis/Convex/Deriv.lean:248`) を使ったので、
  `deriv (deriv f)` の近傍書き換えが 1 度も要らなかった。
- **(c) 2 階微分の符号** (= **gateway atom**) — `gapFunDeriv2_mul` (`:184`) が恒等式
  `gapFunDeriv2 p x · [x(1−x)·u(1−u)] = binEntropy p·(1−2p)²·(x(1−x) − K)` を与える
  (`K := curvatureThreshold p = (L − binEntropy p)·p(1−p) / (binEntropy p·(1−2p)²)`)。
  中身は `u(1−u) = p(1−p) + (1−2p)²·x(1−x)` (`binConv_mul_one_sub`、`ring` 1 行) + `field_simp`。
  ⟹ 符号は `x(1−x) ≥ K` か `≤ K` かだけで決まる (`gapFunDeriv2_nonneg` / `gapFunDeriv2_nonpos`)。
- **(d) ⚠ 起票の参照ルートと逸れた 1 点 — 「符号変化 ≤ 1 回」を `N'(x) > 0` (狭義単調) 経由で書かなかった**。
  代わりに変化点を**閉形で置いた**: `inflection p := (1 − √(max 0 (1 − 4K)))/2`。
  これで `N` の単調性を経由せずに (c) の 2 つの補題へ直接つながり、かつ
  **N10 訂正 5(c) の「符号変化 0 回」の場合が `max 0 (·)` によって自動で吸収される**
  (`1 − 4K < 0` なら `√` の中身が `0` ⟹ `inflection p = 1/2` ⟹ 凸弧が空区間になる)。
  ⚠ **場合分けが要るのは `curvatureThreshold_le_inflection_mul` 1 本だけ**で、そこも
  「`inflection p < 1/2` なら `√` の中身は正 ⟹ `max` が外れる」の 1 行である。
- **(e) 凸弧 `[x₀, 1/2]`** — `gapFunDeriv2 ≥ 0` から `monotoneOn_of_deriv_nonneg`
  (`Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:410`) で `gapFunDeriv` が単調増加 ⟹ `gapFunDeriv ≤ gapFunDeriv(1/2) = 0`
  ⟹ `antitoneOn_of_deriv_nonpos` (`同:479`) で `gapFun` が非増加 ⟹ `gapFun ≥ gapFun(1/2) = 0`。
- **(f) 凹弧 `[0, x₀]`** — `concaveOn_of_hasDerivWithinAt2_nonpos` で `ConcaveOn` を出し、
  `ConcaveOn.min_le_of_mem_Icc` (`Mathlib/Analysis/Convex/Jensen.lean:409`、最小値原理) で
  `min (gapFun 0) (gapFun x₀) ≤ gapFun x`。両端が `≥ 0` (前者は恒等式、後者は (e) から) ⟹ 結論。
  ⚠ **N10 訂正 5(b) の「`δ(x0) ≥ 0` は凸弧側から無料で出る」がそのまま Lean の依存順序になっている**。
- **(g) `[1/2, 1]`** — (a) の対称性 `gapFun p (1−x) = gapFun p x` で `[0,1/2]` に落とす。

⚠ **`Real.strictConcave_binEntropy` / `Real.binEntropy_strictMonoOn` / `Real.binEntropy_strictAntiOn` は
1 度も使っていない** (在庫にはあったが、本ルートでは `binEntropy` 単体の凹性ではなく `gapFun` の 2 階微分が要る)。

---

## 3. 詰まった箇所 / 残った `sorry`

**残った `sorry` = 0 本**。`@residual` = 0 件 (`rg "@residual|sorry" MoreCapableBinary.lean` が 0 hit)。
⟹ **起票の反証条件 (1)「Mathlib の微分 API が届かず自前 build が肥大 ⟹ honest に退出」は不発火**である。

詰まったのは 4 か所で、いずれも数手で抜けた (proof-log 用の記録):

1. **`HasDerivAt.comp` の合成が `Function.comp` の higher-order 単一化で落ちた** —
   `(Real.hasDerivAt_log h).comp x hf` は `?g ∘ f` と `fun y ↦ log (f y)` を単一化できず失敗する。
   `HasDerivAt.log` (`Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean`) に差し替えて解消。
   ⚠ **`binEntropy` 側の合成 (`Real.hasDerivAt_binEntropy _ _ |>.comp`) は同じ形でも通る** —
   こちらは外側関数が具体的 (`Real.binEntropy`) でメタ変数でないため。
2. **`field_simp` が `x * (1-x) ≠ 0` 型の仮説を使えない** — `(1-x)⁻¹` が残る。
   `x ≠ 0` と `1 - x ≠ 0` に**分けて**与えると通る。
3. **`field_simp` が `(1 - 2*p)^2` を `1 - 4p + 4p²` へ ring 正規化してしまい、`(1-2p)^2 ≠ 0` が効かない** —
   分母を `set D := binEntropy p * (1 - 2*p)^2` で原子化してから `field_simp` すると通る。
4. **`rw [heq] at hsq` が `√` の**中身**まで書き換えて goal と食い違う** — `rw [heq] at hsq ⊢` で両側揃える。

⚠ **loogle が空振りしたクエリ**: `Real.sqrt _ < 1` (Found 13 declarations mentioning …, **0 match**)
⟹ `Real.sqrt_lt_one` は無い。`Real.sqrt_lt_sqrt (le_max_left _ _) h` + `Real.sqrt_one` で代替した。

⚠ **自前 build した補題** (Mathlib 不在。起票の見立て「二値畳み込み型の不等式は Mathlib に無い」は当たっている):
`binConv_mul_one_sub` (`u(1−u)` の恒等式) / `gapFunDeriv2_mul` (符号の恒等式) / `inflection` 周りの 4 本 /
`gapFun` の端点 3 本と対称性 1 本 / 微分 3 本 / 弧ごとの結論 4 本。**計 33 本の private 補題**。

---

## 4. ⚠ 確かめて「いない」ことの名指し (⚠⚠ 必須節)

1. ⚠⚠ **レート領域の包含については 1 文字も言っていない**。載ったのは `ℝ` 上の 1 変数不等式 1 本である。
   Lean 側に `Thm7` も `C` も `Ω` も `d*_t` も現れない。
2. ⚠⚠ **[probc] の判定そのものは Lean に載っていない**。載ったのは N10 §2.5 が使った**唯一の解析的入力 1 本**であり、
   N10 §2.1–§2.4 の恒等式群 (`T_t` の 4 項分解 / `ψ_t ≤ d*_t` / `G_t` の閉形) は**1 本も Lean に無い**。
   ⟹ 「`ε = 0` が機械検証された」とは**言えない**。
3. ⚠⚠ **`Thm7 ⊋ C` の材料ではない**。本 leg が出したのは**一致**の側を支える不等式であり、
   分離の側の材料は 1 つも出ていないし、**排除もされていない**。
4. **半空間版は置いた** (§1.2)。⚠ ただし置いたのは `e ≤ h₂(p)` 側だけで、
   **`e > h(p)` 側 (= N10 §4.1 の gate 出力) には手を出していない** (起票 L434 の指示どおり)。
5. ⚠ **領域 def / 計算可能性層 (子 plan `bc-computable-region-formalization-plan.md` の単位 B) には触っていない**
   (起票の反証条件 3 は不発火 — 触る必要が生じなかった)。
6. ⚠ **`δ ≥ 0` が「more capable」であることの**チャネル水準の**言明は Lean に無い**。
   docstring が散文でそう書いているだけで、`IsBCMoreCapable` 系の in-repo 述語との橋は 1 本も無い。
7. ⚠ **等号集合 (零点がちょうど `{0, 1/2, 1}` であること) は載せていない**。載ったのは `≥ 0` だけである
   (N10 §2.5 は零点の特徴づけも書いているが、本 leg の標的ではない)。
8. ⚠ **一次文献 (Mrs. Gerber) との照合はしていない** — N10 §2.5 と同じく、文献を引かずに 2 階微分の符号で閉じた。

---

## 5. 次の leg (敵対的独立監査) が破りに行くべき点 — 自分で最も脆いと思う 3 点

1. ⚠⚠ **「載った命題は本当に N10 の連鎖の入力か」** (= 起票の反証条件 2)。
   本書 §1.4 の `L²·δ` への対応は**本 leg の自前再導出**であり、**N10 §2.5 の `δ` の定義と逐語で突き合わせてはいない**
   (N10 は `δ(x) = C·h₂(x) − h₂(x∗p) + h₂(p)` をビット単位で書き、`C = 1 − h₂(p)` を `e = h₂(p)` の境界で取る)。
   **`C` の取り方 / `e` の境界の位置 / ビットと nat の換算**のどこか 1 か所がずれていれば、載ったのは別物である。
   ⭐ 破り方: N10 §2.5 の `δ` を独立に Python で実装し、本 leg の Lean 標的の左右差 `/ (log 2)²` と
   **有理数の明示点で**突き合わせる (本 leg は float の格子でしか照合していない)。
2. ⚠ **`inflection` の閉形 (§2 の (d)) が起票の参照ルートから逸れている**。
   参照ルートは `N'(x) > 0` による狭義単調 ⟹ 符号変化 ≤ 1 回だが、本 leg は変化点を `√` の閉形で置いた。
   `max 0 (1 − 4K)` の縮退の吸収 (`inflection_mul_le` と `curvatureThreshold_le_inflection_mul` の非対称性 —
   前者は無条件、後者は `inflection p < 1/2` を仮定する) が**本当に全 `p ∈ (0,1/2)` を覆っているか**は
   `gapFun_nonneg` の `rcases le_or_gt y (inflection p)` の 2 分岐だけで担保されている。
   ⚠⚠ **さらに悪いことに、縮退側 (`1 − 4K ≤ 0`) は `p ∈ (0,1/2)` では 1 度も踏まれない** —
   `K` の最大は `p → 1/2` の極限で `0.1803368950 < 1/4` である (10 万点の掃引、上限は解析的には
   `1/(8 log 2) = 0.18033688…`)。⟹ **`max 0 (·)` は決して発火しない防御であり、テストされていない**。
   ⭐ 破り方: 逆に「縮退側が空である」ことに寄りかかった記述が本書のどこかに無いか (無いはずだが) と、
   **踏まれる側**の `inflection_mul_le` (無条件) と `curvatureThreshold_le_inflection_mul`
   (`inflection p < 1/2` 仮定つき) の**非対称が凹弧・凸弧の境界 `x = inflection p` ちょうどで
   両方から使われて矛盾しないか**を突く (`gapFun_nonneg_of_mem_Icc_zero_inflection` は右端で
   `gapFun_nonneg_of_mem_Icc_inflection_two_inv` を呼んでおり、境界点は 2 つの弧に共有されている)。
3. ⚠ **半空間版で仮説 `0 ≤ e` を落としたこと** (§1.2)。
   落として真になるのは `binEntropy x ≥ 0` があるからだが、**`e` に上限も下限も無い**ので
   `e` が大きな負数のとき結論は自明に弱くなる。起票の候補式と**論理的に等価ではない** (本定理の方が強い)。
   ⭐ 破り方: 「起票が求めた形と違う形を置いて『置いた』と書いていないか」を疑う。
   本 leg の主張は「起票の候補式は本定理 + `0 ≤ e` で 1 行で出る」であり、**その 1 行は Lean に書いていない**。

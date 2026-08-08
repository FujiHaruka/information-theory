# N11 — `δ ≥ 0` (more capable の不等式) の層 3 化 (判定枠 第 2 組の第 3 段)

**Parent**: [`bc-open-problem-t3c-plan.md`](bc-open-problem-t3c-plan.md) §5.1 (N11 起票ブロック) /
**前段** = [`bc-t3c-n10-epsilon-zero.md`](bc-t3c-n10-epsilon-zero.md) §2.5 + 訂正 5 (⚠ **論法の SoT はそちら。本書は複製しない**)。

**leg 冒頭宣言 (N11)** (⚠ 起票 §5.1 L414 からの逐語コピー): 側 = (C2) / 動かすもの = §0 が要求する Lean 側 (層 3) を、
N10 の判定を支えている唯一の解析的入力 `δ ≥ 0` の分だけ動かし、判定枠 第 2 組が散文で閉じた解析核が機械検証された状態にする

> **着地** = `InformationTheory/Shannon/BroadcastChannel/MoreCapableBinary.lean` (新規 410 行、35 宣言、`sorry` **0**)。
> **標的 1 本 + 半空間版 1 本の計 2 本**が `@[entry_point]` で載り、両方 **sorryAx-free** である。
> ⚠⚠ **落としてはならない限定は §4 に全部書いた** — 載ったのは**実数変数レベルの 1 変数不等式 1 本**であって、
> **レート領域の包含についても [probc] の判定そのものについても 1 文字も言っていない**。

> ⭐ **敵対的独立監査 (親 plan §4.6) 済み** = [`bc-t3c-n11-audit.md`](bc-t3c-n11-audit.md) /
> 監査側の独立検証器 `docs/shannon/verifiers/n11_audit_morecapable.py` (**43/43**、⚠ 生のチャネル同時分布からの
> 再導出 + 有理点 12 個の区間演算を含む) / 監査側の Lean probe
> `docs/shannon/probes/t3c-n11/more-capable-binary-audit.lean` (`lake env lean` **EXIT=0**)。
> **判定 = 訂正あり生存** (破りに振った **49 系統のうち 43 系統が潰せず・6 系統が成立**、訂正 7 件。
> ⚠⚠ **主判定 (「`δ ≥ 0` が 0 sorry / sorryAx-free で層 3 に載り、それは N10 の連鎖が実際に消費する各点版である」)
> を動かす訂正は 0 件**)。⚠ **本文は訂正 7 件を反映済**である (§1.1 = 訂正 3 / §1.2 = 訂正 4・5 /
> §1.5 = 訂正 7 / §1.6 = 訂正 6 / §2 (d) と §5-2 = 訂正 1・2 / §4 = 監査 §3 との突き合わせ)。
> ⚠ **leg 冒頭宣言は事後に書き換えない** — 訂正 6 (「唯一の解析的入力」という枠付けの限定) の効きは §1.6 が担う。
> ⭐ **honesty の 4 check はすべて PASS** (`sorry` 0 / 独自 `axiom` 0 / load-bearing hypothesis 0 /
> 非退化を機械証明) ⟹ 2 本の `@[entry_point]` 定理の docstring に `@audit:ok` (tier 1) を付した。

---

## 1. 載ったもの

**ファイル**: `InformationTheory/Shannon/BroadcastChannel/MoreCapableBinary.lean` (新規)。
**配線**: `InformationTheory.lean` L134 に `import` を追記済 (`OuterBoundTransport` の直後)。

### 1.1 標的 (起票 §5.1 L419–L423 の逐語形)

`MoreCapableBinary.lean:381`:

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

⚠⚠ **監査 訂正 3 — `p` の仮説 2 本は落とせる (⚠ ただしこれは記述の訂正であって射程の拡大ではない)**。
`0 < p` と `p < 1/2` は **どちらも落とせ、命題は `p ∈ [0,1]` の全体で真**である。機械証明は監査の Lean probe
`docs/shannon/probes/t3c-n11/more-capable-binary-audit.lean` にある (`1/2 < p < 1` は `Real.binEntropy_one_sub` の
対称性 3 行、`p ∈ {0, 1/2, 1}` はいずれも等号)。⚠ **`[0,1]` の外では偽である** (`p = 1.1, x = 0.295` で左右差 `−0.0013692`)
⟹ honest な定義域は `[0,1]` ちょうどである。
⚠⚠ **情報理論的な中身は 1 つも増えない** — `BSC(1−p)` は `BSC(p)` の出力ラベルの付け替えであり、
`p ∈ {0, 1/2, 1}` は退化チャネルである。
⭐ **設計判断 = 署名は起票の逐語形 (`0 < p`, `p < 1/2`) のまま据え置く** (情報理論的な定義域を保つ /
消費者がまだ 1 本も無いので緩めても誰も得をしない)。
⟹ 正確な記述は **「`p < 1/2` は必要ではないが、落とさずに置いてある」**である
(⚠ **`p < 1/2` が必要であるかのように読ませない**)。

### 1.2 半空間版 (起票 §5.1 L425 の「候補」— **置いた**)

`MoreCapableBinary.lean:396`:

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

⭐ **監査 訂正 4 — 自己申告の穴は閉じた**。§5-3 が「その 1 行は Lean に書いていない」と自己申告していた段は、
監査の probe `n11_ticket_candidate_form` が**機械証明**した (⚠ **linter 警告
「`he₀` is not explicitly referenced」自体が「`0 ≤ e` は証明に 1 度も使われない」ことの機械証拠**である)。
⭐ **逆向き `n11_main_from_halfspace` (半空間版を境界 `e = binEntropy p / log 2` で使うと §1.1 の標的が戻る) も
機械証明済**である ⟹ **2 本の `@[entry_point]` は互いに導出可能**であり、片方だけが真という食い違いは無い。
⚠ **この 2 本は probe に留まり、Lean の本体 (層 3) には載っていない**。

⚠ **監査 訂正 5 — 仮説 `he` の構造の注記 (⚠⚠ 循環ではない)**。`he : e * Real.log 2 ≤ Real.binEntropy p` は
**その結論の `x = 2⁻¹` の場合と命題として同値**である (`binConv p 2⁻¹ = 2⁻¹` ゆえ結論が
`log 2 − binEntropy p ≤ (1−e)·log 2` に潰れる)。
⚠⚠ **これは循環ではない** — 定理の内容は「1 点の場合 ⟹ `[0,1]` 全体」という**増幅**であり、
body も `he` を単調性の入力として実際に消費している (`:403–406`)。
さらに `he` は**必要条件**でもある (`e > h₂(p)` では `x = 1/2` で偽、実測 `−0.0069315`)
⟹ ⭐ **`he` は最も弱い十分条件であり、同時に必要条件である**。
⚠ **後の読み手が「仮説 ≡ 結論の 1 インスタンス」を defect と誤認しないための記録**である。

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
⚠ **監査 訂正 7 の効き**: 転記の正しさを支える最良の証拠は本節の float 格子ではなく **§1.5 の tightness** である。
⭐ **有理点での厳密な照合は監査が埋めた** (`B3`/`F2`: N10 §2.5 の `δ` を独立に実装し、
`Lean の左右差 / (log 2)²` と有理点で残差 `6.9953e-42` で一致)。

### 1.5 ⭐ tightness — 載ったのは `e` について最も鋭い 1 本である (監査 訂正 7 = 上方修正)

監査の probe `n11_tight_at_two_inv` が示すとおり、⭐ **すべての `p` について `x = 2⁻¹` で両辺は等しい**
(`Real.binEntropy_two_inv` + `ring`。`binConv p 2⁻¹ = 2⁻¹` ゆえ両辺とも `log 2 − binEntropy p` に潰れる)。
⟹ **載ったのは「ある真な不等式」ではなく、`e` のスロットについて最も鋭い 1 本**である
(`e` を `h₂(p)` より少しでも大きく取れば `x = 2⁻¹` で偽になる — §1.2 の訂正 5)。

⚠⚠ **これが「単位の取り違え」を数値に頼らずに消す最良の証拠である**。bit / nat の取り違えの一方向
(`e := binEntropy p` を `e` のスロットへ置く読み) は**真だが緩い**命題を作る (`x = 1/2` で余裕 `0.060915`、監査 `B5`)
⟹ ⚠ **コンパイルが通ったことだけでは単位は pin されない**。pin しているのは本節の等号と、
監査が有理点で取った厳密一致の 2 つである (§1.4 の float 格子ではない)。

### 1.6 ⚠⚠ 「唯一の解析的入力」という枠付けの限定 (監査 訂正 6)

本書冒頭の leg 冒頭宣言は起票 §5.1 L414 の逐語コピーであり、そこで `δ ≥ 0` は
「N10 の判定を支えている**唯一の**解析的入力」と枠付けされている。⚠ **この「唯一の」は無条件には書けない** —
N10 §2.4 は `σ_x := d*_t − ψ_t(x) ≥ 0` も併用しており、これは `d*_t` が**最大値として達成される**ことに依る
(連続関数 + コンパクト集合ゆえ、厳密には代数ではない)。
⚠ **これは N10 からの継承であって本 leg が作った誤りではない** / ⚠ **監査もこの点を再導出していない** (監査 §3-1)。
⟹ **本書で書いてよいのは「N10 §2.5 が使った解析的入力を載せた」までであり、
「N10 の解析的入力を全部載せた」ではない**。⚠ **冒頭宣言と起票ブロックは事後に書き換えない** (効きは本節が担う)。

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
  ⚠ **監査 訂正 2**: 縮退枝 (`1 − 4K ≤ 0`) が `p ∈ (0,1/2)` で踏まれるかどうかは**健全性に無関係**である —
  `K < 1/4` を要求する補題は 1 本も無く、**kernel は到達不能枝も含めて両枝を検査している** (§5-2)。
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

**⚠ 監査 §3 との突き合わせで追加された 5 点** (⚠ **監査自身が確かめていないことの逐語 SoT は
[`bc-t3c-n11-audit.md`](bc-t3c-n11-audit.md) §3**):

9. ⚠⚠ **N10 §2.2–§2.4 の恒等式群 (`T_t` の 4 項分解 / `S_A` / `S_B` / `σ` の非負性) は、本 leg も監査も再導出していない**。
   確かめられたのは「それらが消費するのは各点の `δ ≥ 0` である」という**接続**だけである (監査 `F1` / `F3`)
   ⟹ **N10 の恒等式に誤りがあれば本 leg も監査も同じ誤りを共有する**。§1.6 の `d*_t` の達成性も未検証である。
10. ⚠ **`K < 1/4` を厳密な方法で全 `p ∈ (0,1/2)` について証明していない** (掃引 + 極限 + 単調性はいずれも screen)。
    ⚠ **訂正 2 により、この事実は健全性に無関係である** (§5-2)。
11. ⚠ **Lean の証明を 1 行ずつ検証した者はいない** — 導出の正しさは kernel (`lake env lean` + `#print axioms`) に委ねている。
    監査が private 補題を読んだのは「どの補題が `K < 1/4` を要求するか」という**構造**の確認のためである。
12. ⚠ **数値の残差は有理点 12 個 (監査の区間演算) を除きすべて浮動小数**であり、保証された誤差上界ではない。
    ⚠ **格子掃引・局所降下・近零点の探索は screen** であって証拠ではない (非違反は「まだ見つかっていない」以上を言わない)。
13. ⚠ **訂正 3 の拡張 (`p ∈ [0,1]`) は Lean の本体に載っていない** — 監査 probe の 4 定理に留まる (§1.1)。
    ⚠ **訂正 4 の 2 本 (起票の候補式 / 逆向き) も同じく probe 留まりである** (§1.2)。

---

## 5. 事前に「最も脆い」と挙げた 3 点と、監査が実際に当てた結果

⚠ **3 点の本文は監査の着手前に書いたものである** (較正のために主部はそのまま残す)。
⚠ **監査の逐語の SoT は [`bc-t3c-n11-audit.md`](bc-t3c-n11-audit.md)** であり、以下の「**結果**」はその要約である。
⚠ **項 2 だけは本文を訂正した** — 事実として誤っていた数値 1 つと、脆弱性でないものを脆弱性と書いた自己評価 1 つを
そのまま残すことは較正ではないからである (何をどう書いていたかは訂正の側に逐語で残した)。

1. ⚠⚠ **「載った命題は本当に N10 の連鎖の入力か」** (= 起票の反証条件 2)。
   本書 §1.4 の `L²·δ` への対応は**本 leg の自前再導出**であり、**N10 §2.5 の `δ` の定義と逐語で突き合わせてはいない**
   (N10 は `δ(x) = C·h₂(x) − h₂(x∗p) + h₂(p)` をビット単位で書き、`C = 1 − h₂(p)` を `e = h₂(p)` の境界で取る)。
   **`C` の取り方 / `e` の境界の位置 / ビットと nat の換算**のどこか 1 か所がずれていれば、載ったのは別物である。
   ⭐ 破り方: N10 §2.5 の `δ` を独立に Python で実装し、本 leg の Lean 標的の左右差 `/ (log 2)²` と
   **有理数の明示点で**突き合わせる (本 leg は float の格子でしか照合していない)。
   ⟹ **結果 = 不成立 (最も疑って掛かられた系統だが耐えた)**。監査は指定どおりの破り方を実行し
   (`B3`/`F2`: N10 §2.5 の `δ` を独立実装して**有理点で**照合、残差 `6.9953e-42`)、さらに
   **`F1` が「N10 §2.3 の `S_A = e·δ(a) + C·E[δ(A)]` は各点の `δ ≥ 0` を要し、`δ` が 1 点でも負なら
   `S_A < 0` になる (実測 `−0.05`)」ことを確かめた** ⟹ **載ったのは平均版でも有限点版でもなく、
   まさに必要な各点版である** (`F3`: N10 が `δ` に渡す 6 引数はすべて `[0,1]` ⟹ 被覆)。
   ⚠ **§1.4 の float 格子は照合として不足していた** — 埋めたのは監査の側である。
2. ⚠ **`inflection` の閉形 (§2 の (d)) が起票の参照ルートから逸れている**。
   参照ルートは `N'(x) > 0` による狭義単調 ⟹ 符号変化 ≤ 1 回だが、本 leg は変化点を `√` の閉形で置いた。
   `max 0 (1 − 4K)` の縮退の吸収 (`inflection_mul_le` と `curvatureThreshold_le_inflection_mul` の非対称性 —
   前者は無条件、後者は `inflection p < 1/2` を仮定する) が**本当に全 `p ∈ (0,1/2)` を覆っているか**は
   `gapFun_nonneg` の `rcases le_or_gt y (inflection p)` の 2 分岐だけで担保されている。
   ⭐ 破り方: **踏まれる側**の `inflection_mul_le` (無条件) と `curvatureThreshold_le_inflection_mul`
   (`inflection p < 1/2` 仮定つき) の**非対称が凹弧・凸弧の境界 `x = inflection p` ちょうどで
   両方から使われて矛盾しないか**を突く (`gapFun_nonneg_of_mem_Icc_zero_inflection` は右端で
   `gapFun_nonneg_of_mem_Icc_inflection_two_inv` を呼んでおり、境界点は 2 つの弧に共有されている)。
   ⟹ **結果 = 不成立 (境界は矛盾しない)**。監査が構造を確認した — 左弧は無条件の `inflection_mul_le`、
   右弧は**開区間の内点でのみ** `curvatureThreshold_le_inflection_mul` を呼ぶ
   (`hy : y ∈ Ioo (inflection p) 2⁻¹` から `inflection p < 2⁻¹` を取り出す) ⟹ 非対称は両立する。
   ⚠ **最終的な担保は kernel である**。符号変化がちょうど 1 回であること・その位置が `inflection p` であることも
   6 個の `p` で確認された (`C9`/`C10`、⚠ screen)。

   ⚠⚠ **訂正 2 (監査 `B7`、自己評価が過大に悲観だった)** — 本項には当初
   「**縮退側 (`1 − 4K ≤ 0`) は `p ∈ (0,1/2)` では 1 度も踏まれない ⟹ `max 0 (·)` は決して発火しない防御であり、
   テストされていない**」と書き、破り所として名指ししていた。**これは脆弱性ではない** —
   Lean を読むと **`K < 1/4` を要求する補題は 1 本も無く** (`inflection_pos` は `K > 0` のみ /
   `inflection_mul_le` は無条件 / `curvatureThreshold_le_inflection_mul` は `inflection p < 2⁻¹` から `max` を外す)、
   ⚠⚠ **kernel は到達不能枝も含めて両枝を検査している** ⟹ **仮に `K ≥ 1/4` になる `p` があっても
   壊れる箇所は名指しできない** (凸弧が空区間になるだけである)。⟹ **本項は「監査が突くべき点」から降格する**。

   ⚠ **訂正 1 (監査 `B6`、数値の誤り)** — 本項には当初「`K` の最大は `p → 1/2` の極限で **`0.1803368950`**」と
   「上限は解析的には `1/(8 log 2) = 0.18033688…`」を併記していたが、⚠⚠ **前者は後者を `1.5e-8` 上回っており
   内部矛盾していた** (自分で引いた上限を超える「最大値」は原理的にありえない)。
   正しいのは後者の側で、**`sup K = 1/(8 log 2) = 0.1803368801111204`** である
   (掃引値は float64 の桁落ち artefact — 監査が float64 で 10 万点を掃くと `0.18033699511887788` (`p = 0.49999`) が出て
   **同じ型の artefact を再現した**。40 桁では `0.1803368801`)。
   さらに `K` は `(0,1/2)` 上で**狭義単調増加**なので、`1/(8 log 2)` は **達成されない上限**であって「最大」ではない。
   ⚠ **`K < 1/4` の結論は動かない**。
3. ⚠ **半空間版で仮説 `0 ≤ e` を落としたこと** (§1.2)。
   落として真になるのは `binEntropy x ≥ 0` があるからだが、**`e` に上限も下限も無い**ので
   `e` が大きな負数のとき結論は自明に弱くなる。起票の候補式と**論理的に等価ではない** (本定理の方が強い)。
   ⭐ 破り方: 「起票が求めた形と違う形を置いて『置いた』と書いていないか」を疑う。
   本 leg の主張は「起票の候補式は本定理 + `0 ≤ e` で 1 行で出る」であり、**その 1 行は Lean に書いていない**。
   ⟹ **結果 = 成立 (自己申告の穴を監査が閉じた) = 訂正 4** (§1.2)。監査が probe `n11_ticket_candidate_form` を書いて
   機械証明し、⭐ **逆向き `n11_main_from_halfspace` も機械証明した** ⟹ **2 本の `@[entry_point]` は互いに導出可能**。
   ⚠ **落とした側が真に強いという本項の読み自体は覆っていない** — 監査 `E6` が
   `e = −0.001 / −1 / −100` でも結論が真であることを確かめており、これはその機械確認である。
   ⚠ **構造の注記 (訂正 5) はここではなく §1.2 に置いた** — `he` は最も弱い十分条件であり同時に必要条件である、
   という記録は宣言のすぐ隣に無いと読み手が defect と誤認しうるからである。

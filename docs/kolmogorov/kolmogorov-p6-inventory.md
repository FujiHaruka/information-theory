# Ch.14 Kolmogorov — Phase P6 (非圧縮列の SLLN, CT Thm 14.5.1) Mathlib + in-project API 台帳

> **Status**: INVENTORY (2026-07-25)。P6 stretch(`Incompressible.lean` 新規)着手前台帳。
> **親**: [`kolmogorov-moonshot-plan.md`](kolmogorov-moonshot-plan.md) §Phase P6(retreat 出口 = `sorry + @residual(plan:kolmogorov-slln)`)。
> **消費する counting core**: `condIncompressible_count`(`Counting.lean:176`)。
> 全 Mathlib `file:line` は `.lake/packages/mathlib/` 実体を Read して確認、in-project は該当行を Read して確認。
> loogle は index (`.lake/build/loogle.index`) 経由でクエリした結果を verbatim 転記。

## 一行サマリ

**P6 の make-or-break である「二値エントロピー × 二項係数」上界(item B、`C(n,k) ≤ 2^{n·H(k/n)}`)は
Mathlib に直接の lemma としては不在**(loogle `Nat.choose, Real.binEntropy` → **Found 0**、Mathlib の choose
指数上界は trivial な `Nat.choose n k ≤ 2^n` 止まり)。**しかし同じ内容が in-project に既存**
(`typeClassByCount_card_le` + `pow_div_prod_pow_eq_exp_n_entropyByCount` + `entropyByCount`、P4 上界が
まさにこの鎖を消費)であり、**α = Bool へ特殊化 + `entropyByCount = binEntropy` の橋 15–25 行で item B は賄える**。
**item A(`Nat.choose` への還元)・item C(二項裾)はいずれも P6 の pointwise(単一 type-class)ルートでは不要。**

- **item B は self-build ではなく「既存 in-project 資産の refactor + Bool 特殊化」**。closest asset = P4 上界の per-string
  補題 `condComplexity_block_typical_le`(`EntropyRate.lean:418`)で、その内部が item B の鎖を verbatim に使っている。
- 数え上げ core(`condIncompressible_count`)は既存・`@audit:ok`。
- **P6 は measure-free**(pointwise/deterministic)— P4 と違い `μ`/`Xs`/i.i.d. 仮定を **一切継承しない**
  (per-string 上界は純粋に組合せ的で `invariance` / `typeDecoder` / `typeClassByCount_card_le` のみに依存)。
- **見積**: 新規 ~150–250 行(raw per-string 上界 refactor 40–60 + Bool 橋 15–25 + 解析「H→log2 ⟹ p→1/2」40–70 +
  文言/組立 40–80)。**genuine Mathlib 壁は無い**(第 2 波 prefix 塔とは無関係)。

---

## 主定理の最終形(想定 = planner が確定)+ 証明戦略

CT 2nd ed **Thm 14.5.1**。番号・正確な quantifier は planner が原典照合で確定するが、Mathlib-shape-driven の観点で
**`Nat.choose` でなく `typeCount`/`entropyByCount`/`Real.binEntropy` で framing する**のが最短(item A 回避)。想定形:

```lean
-- 頻度 p(b) := (b が true を取る座標数) / n = (typeCount b true : ℝ) / n
-- 「δ 近傍」形(contrapositive route、fixed-gap で扱いやすい):
theorem incompressible_freq_tendsto_half
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ b : Fin n → Bool,
      (n : ℝ) ≤ (condComplexity (encodeBlock n b) n : ℝ) →      -- 非圧縮性(bit 基底で ≥ n)
        |((typeCount b true : ℝ) / n) - 2⁻¹| < δ
```

証明戦略(pseudo-Lean、6–10 行):

```
-- (1) raw per-string 上界(P4 上界の refactor、typicality を落とす):任意 b で
C(encodeBlock n b | n) ≤ (card Bool)·logb 2 (n+1) + n·entropyByCount(typeCount b)/log2 + c_dec
-- (2) Bool 橋:entropyByCount(typeCount b) n = binEntropy ((typeCount b true)/n)    ← 自作 15–25 行
-- (3) 非圧縮性 n ≤ RHS と (1)(2) を合成し binEntropy(p) ≥ log2·(1 - o(1)) を得る
n ≤ 2·logb 2 (n+1) + n·binEntropy(p)/log2 + c   ⟹   binEntropy(p) ≥ log2 - o(1)
-- (4) contrapositive の解析核(fixed gap):|p - 1/2| ≥ δ ⟹ binEntropy(p) ≤ binEntropy(1/2-δ) < log2
--     γ(δ) := log2 - binEntropy(1/2-δ) > 0(binEntropy_strictMonoOn/strictAntiOn + binEntropy_two_inv_add)
-- (5) o(1) < γ(δ) が eventually 成立 ⟹ 非圧縮なら |p-1/2| < δ。□
```

---

## API 在庫テーブル

status 凡例: ✅ 既存 / ⚠️ 既存だが噛み合わせ注意 / ❌ 不在(自作)。`[...]` 型クラス前提・結論形は **verbatim**。

### A. 二項係数による「1 の個数 = k」の数え上げ(popcount → C(n,k))

> **P6 では不要(item D の `entropyByCount` ルートが `Nat.choose` を経由しない)。** framing を `Nat.choose` にする場合のみ橋が要る。参考として掲載。

| 概念 | API(verbatim) | file:line | status | P6 での扱い |
|---|---|---|---|---|
| k 元部分集合の数 | `theorem Finset.card_powersetCard (n : ℕ) (s : Finset α) : card (powersetCard n s) = Nat.choose (card s) n` | `Mathlib/Data/Finset/Powerset.lean:212` | ✅ | `#{S ⊆ Fin n // #S = k} = C(n,k)`。Bool 列 ↔ 部分集合の橋を作れば使える |
| 型クラス(count 固定) | `def typeClassByCount {n : ℕ} (c : α → ℕ) : Set (Fin n → α) := { x | ∀ a, typeCount x a = c a }` | `InformationTheory/Shannon/Sanov/LDP.lean:79` | ✅ | **Bool + `c true = k` で「k 個 true の列」= C(n,k) の実体**。P6 の対象集合 |
| 個数関数 | `noncomputable def typeCount {n : ℕ} (x : Fin n → α) (a : α) : ℕ := (Finset.univ.filter (fun i : Fin n ↦ x i = a)).card` | `InformationTheory/Shannon/Sanov/Basic.lean:53` | ✅ | `typeCount b true` = b の 1 の個数 |
| 個数総和 = n | `sum_typeCount b : (∑ a, typeCount b a) = n`(P4 で使用、`EntropyRate.lean:447` から参照) | `InformationTheory/Shannon/Sanov/*` | ✅ | Bool 橋で `c false = n - c true` を出すのに必須 |
| **`typeClassByCount(Bool,k)` の card = `C(n,k)`** | — | — | ❌ **不在** | **item D ルートでは不要**。`Nat.choose` framing 時のみ自作橋(~20–40 行) |

### B. 二項係数の二値エントロピー上界(**item B = crux**)

| 概念 | API(verbatim) | file:line | status | P6 での扱い |
|---|---|---|---|---|
| **`C(n,k) ≤ 2^{n·H(k/n)}` の直接 lemma** | — | — | ❌ **Mathlib 不在**(loogle Found 0、§walls) | **in-project で代替**(下 2 行) |
| **raw card 上界(一般 α)** | `theorem typeClassByCount_card_le {n : ℕ} (c : α → ℕ) (hc_sum : (∑ a, c a) = n) : ((typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card : ℝ) ≤ (n : ℝ) ^ n / ∏ a : α, ((c a : ℝ) ^ (c a))` | `InformationTheory/Shannon/Sanov/MultinomialLowerBound.lean:677` | ✅ | **item B の実体(前半)**。`[Fintype α] [DecidableEq α] [Nonempty α]` |
| **exp 橋(raw → exp(n·H))** | `lemma pow_div_prod_pow_eq_exp_n_entropyByCount {n : ℕ} (c : α → ℕ) (hc_sum : (∑ a, c a) = n) : (n : ℝ) ^ n / ∏ a : α, ((c a : ℝ) ^ (c a)) = Real.exp ((n : ℝ) * entropyByCount c n)` | `InformationTheory/Shannon/TypeClassLowerBound.lean:55` | ✅ | `@[entry_point]`。上 2 つを合成 ⟹ `|T_c| ≤ exp(n·entropyByCount c n)` |
| 経験エントロピー | `noncomputable def entropyByCount (c : α → ℕ) (n : ℕ) : ℝ := -∑ a : α, ((c a : ℝ) / n) * Real.log ((c a : ℝ) / n)` | `InformationTheory/Shannon/TypeClassLowerBound.lean:38` | ✅ | `@[entry_point]`。**Bool で `= binEntropy(k/n)`(自作橋)** |
| `Real.binEntropy` | `@[pp_nodot] noncomputable def binEntropy (p : ℝ) : ℝ := p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹` | `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean:63` | ✅ | `Real.log`(nat 基底)。最大値 `log 2` at `p = 2⁻¹` |
| choose の trivial 指数上界 | `theorem Nat.choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n` | `Mathlib/Data/Nat/Choose/Bounds.lean:96` | ✅(だが弱すぎ) | **P6 には無力**(集中を出せない = 全 k で `2^n`)。参考 |
| choose の `n^k` 上界 | `lemma Nat.choose_le_pow (n k : ℕ) : n.choose k ≤ n ^ k` | `Bounds.lean:54` | ✅(弱) | 同上 |
| choose ≤ n^k/k! | `theorem Nat.choose_le_pow_div (r n : ℕ) : (n.choose r : α) ≤ (n ^ r : α) / r !` [`[Semifield α] [LinearOrder α] [IsStrictOrderedRing α]`] | `Bounds.lean:34` | ✅(弱) | Stirling 経由で H 上界を自作する場合の下地(採らない) |

**item B verdict**: 直接 lemma は不在。**しかし `typeClassByCount_card_le` ∘ `pow_div_prod_pow_eq_exp_n_entropyByCount`
が一般 α で `|T_c| ≤ exp(n·entropyByCount c n)` を与え、α = Bool + `entropyByCount = binEntropy` 橋で
`C(n,k) ≤ exp(n·binEntropy(k/n)) = 2^{n·binEntropy(k/n)/log2}` になる。P4 上界がこの鎖を verbatim に使っている**
(`EntropyRate.lean:445–452`)ので **self-build 相当の新規数学は無い**。

### C. 二項裾 / 集中(binomial tail)

> **P6 の pointwise(単一 type-class)ルートでは不要。** 「全 k について裾和 ≤ 2^n·exp(-cδ²n)」は使わず、
> 非圧縮性が破れる **単一の type k** に対して binEntropy < log2 を出す。参考として Mathlib 資産を掲載。

| 概念 | API(verbatim) | file:line | status | P6 での扱い |
|---|---|---|---|---|
| Chernoff(MGF 経由) | `theorem ProbabilityTheory.measure_ge_le_exp_mul_mgf [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t) …` | `Mathlib/Probability/Moments/Basic.lean:429` | ✅(確率形) | 組合せ的 choose 裾ではない。P6 では不使用 |
| Hoeffding(sub-Gaussian 和) | `lemma ProbabilityTheory.measure_sum_ge_le_of_iIndepFun {ι} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) …` | `Mathlib/Probability/Moments/SubGaussian.lean:780` | ✅(確率形) | 同上 |
| **組合せ的 `∑_{tail} C(n,k) ≤ 2^n·(→0)`** | — | — | ❌ 不在 | **不要**(pointwise route が回避)。参考 template = 下行 |
| 中心二項の和上界(近い形) | `theorem Nat.choose_middle_le_pow (n : ℕ) : (2 * n + 1).choose n ≤ 4 ^ n` | `Mathlib/Data/Nat/Choose/Sum.lean:116` | ✅ | 「和で choose を挟む」証明の唯一の近縁 template |
| 中央 choose が最大 | `theorem Nat.choose_le_middle (r n : ℕ) : choose n r ≤ choose n (n / 2)` | `Mathlib/Data/Nat/Choose/Basic.lean:333` | ✅ | H の単峰性の離散版(解析は binEntropy_strictMonoOn を使う) |

### D. in-project 再利用(P4 上界機械 = item B の実体)

> **loogle は Mathlib のみを見るため in-project は `rg`/Read で確認。ここが P6 の主戦力。**

| 概念 | API(verbatim) | file:line | status | P6 での扱い |
|---|---|---|---|---|
| **消費する counting core** | `theorem condIncompressible_count (y k : ℕ) : {x : ℕ | condComplexity x y < k}.ncard < 2 ^ k` (`@audit:ok`) | `InformationTheory/Shannon/Kolmogorov/Counting.lean:176` | ✅ | 「非圧縮列の存在」に使う(全 2^n 列中 < 2^n が圧縮可 ⟹ ∃ 非圧縮)。**P6 本体は上界方向なので主役ではない** |
| ブロック符号化 | `noncomputable def encodeBlock (m : ℕ) (x : Fin m → α) : ℕ := (finFunctionFinEquiv fun i ↦ Fintype.equivFin α (x i)).val` | `EntropyRate.lean:63` | ✅ | `b : Fin n → Bool` を ℕ 化して `condComplexity` へ |
| 符号化 injective | `theorem encodeBlock_injective (m : ℕ) : Function.Injective (encodeBlock (α := α) m)` | `EntropyRate.lean:67` | ✅ | |
| 符号化 < card^m | `theorem encodeBlock_lt (m : ℕ) (x : Fin m → α) : encodeBlock (α := α) m x < Fintype.card α ^ m` | `EntropyRate.lean:75` | ✅ | Bool で `< 2^n`(全列が [0,2^n) に入る = 存在論の分母) |
| **型復号器**(Partrec₂) | `noncomputable def typeDecoder (m n : ℕ) : Part ℕ` | `EntropyRateUpper.lean:77` | ✅ | (型記述子, index)から元の block を復元。per-string 上界の核 |
| 復号器の Partrec 性 | `theorem typeDecoder_partrec : Partrec₂ (typeDecoder (α := α))` | `EntropyRateUpper.lean:162` | ✅ | `invariance` に食わせる(加法定数 `b_c`) |
| **型復号器の witness 存在** | `theorem exists_mem_typeDecoder_lt {n : ℕ} (hn : 0 < n) (b : Fin n → α) : ∃ m : ℕ, encodeBlock n b ∈ typeDecoder (α := α) m n ∧ m < (n + 1) ^ Fintype.card α * (typeClassByCount (n := n) (typeCount b)).toFinite.toFinset.card` | `EntropyRate.lean:311` | ✅ | **記述数 m < K·\|T_c\|**。per-string 上界の主命題 |
| **P4 per-string 上界(typical)** | `theorem condComplexity_block_typical_le (hXs) (hpos) {ε} (hε) {δ} (hδ) : ∀ᶠ n in atTop, ∀ b, b ∈ stronglyTypicalSet μ Xs n ε → (condComplexity (encodeBlock n b) n : ℝ) ≤ (n:ℝ)*((entropy μ (Xs 0) + ε*logSumAbs μ Xs)/Real.log 2) + (n:ℝ)*δ` | `EntropyRate.lean:418` | ⚠️ | **P6 raw 上界の直接の親**。内部(445–452 行)が item B の鎖を使う。**typicality を落とした raw 版を自作**(下 §自作) |
| P4 uniform 上界 | `theorem condComplexity_block_uniform_le : ∃ C, 0 ≤ C ∧ ∀ (n) (b), (condComplexity (encodeBlock n b) n : ℝ) ≤ C * ((n:ℝ)+1)` (`@audit:ok`) | `EntropyRate.lean:502` | ✅ | measure-free。P6 の「O(n) 粗上界」保険に流用可 |
| typicality → H 束縛 | `theorem entropyByCount_le_of_strongTypical (hXs) {n} (hn) {ε} (x) (hx) (hpos) : entropyByCount (typeCount x) n ≤ entropy μ (Xs 0) + ε * logSumAbs μ Xs` | `EntropyRate.lean:394` | ⚠️ | **P6 では使わない**(この step を落とすのが raw 版)。P6 は `entropyByCount` を一般のまま残す |
| natLen(bit 長) | `def natLen`(`(encodeNat m).length` 相当)/ `theorem natLen_le` | `EntropyRate.lean`(P4 内、`natLen_le m hmpos : 2^natLen m ≤ 2*m`) | ✅ | 記述数 m → bit 長。per-string 上界の中間 |

**item B の実体は §D の `condComplexity_block_typical_le` 内部にある**:445–449 行が
`typeClassByCount_card_le` + `pow_div_prod_pow_eq_exp_n_entropyByCount` で `|T_c| ≤ exp(n·entropyByCount)` を作り、
450–452 行だけが `entropyByCount_le_of_strongTypical`(typicality)で `≤ H+εL` に落とす。**P6 は 450–452 を外し
`entropyByCount(typeCount b)` を残すだけ** ⟹ raw per-string 上界(measure-free、全 b)。

---

## Key-preconditions box(事故が起きやすい前提)

- **P6 は measure-free(P4 と最大の差)**: raw per-string 上界(item D)は `μ`/`Xs`/i.i.d.(`iIndepFun`+`Pairwise ⟂`+
  `IdentDistrib`)を **一切必要としない**。`invariance` / `typeDecoder_partrec` / `exists_mem_typeDecoder_lt` /
  `typeClassByCount_card_le` / `pow_div_prod_pow_eq_exp_n_entropyByCount` は全て純組合せ的。**P6 signature に
  probability 仮定を継承させないこと**(継承すると load-bearing でない冗長 hyp = under/over いずれでもないが不要な結合)。
- **`typeClassByCount_card_le` / `entropyByCount` の型クラス**: `[Fintype α] [DecidableEq α] [Nonempty α]`
  (+ `entropyByCount` は変数ブロック上 `[MeasurableSpace α] [MeasurableSingletonClass α]` も要求)。
  **α = Bool は全 instance 自動導出**(`Fintype Bool`/`DecidableEq Bool`/`Nonempty Bool`/離散 `MeasurableSpace`)。
- **`entropyByCount` / `binEntropy` は nat 基底(Real.log)**: `binEntropy_two_inv : binEntropy 2⁻¹ = log 2`。
  複雑性は **bit 基底**(`2^·`)。非圧縮閾値 `n`(bit)と `binEntropy`(nat)を繋ぐ **`/ Real.log 2`** の掛け合わせが
  per-string 上界に必須(P4 と同じ `Real.log 2` plumbing、`log_two_pos`/`two_pow_eq_exp` が `EntropyRate.lean:89–92` に既存)。
- **`sum_typeCount b : ∑ a, typeCount b a = n` が Bool 橋の前提**: `entropyByCount = binEntropy` を出すには
  `c false = n - c true` が要り、これは `sum_typeCount`(既存)から。`n = 0` の退化に注意(`binEntropy` の `0/0` 規約 =
  `Real.log 0 = 0` で両辺 0、`entropyByCount c 0 = 0` は `pow_div_prod_pow_eq_exp_n_entropyByCount` の n=0 分岐で既済)。
- **`Nat.sInf` / `condComplexity` の非空性**: P6 は `condComplexity` を上から評価するので `sInf_le`(`Nat.sInf_le` は
  `protected`、フル修飾)を使う。`x ∈ universalEval p y` の `∈` は `Part.Mem`(既存 Counting.lean と同規約)。

---

## 自作が必要な要素(優先度順)

1. **【crux】raw per-string 上界(typicality を落とす)** ~40–60 行
   ```lean
   theorem condComplexity_block_le_entropyByCount {n : ℕ} (hn : 0 < n) (b : Fin n → α) :
       (condComplexity (encodeBlock n b) n : ℝ)
         ≤ (Fintype.card α : ℝ) * Real.logb 2 ((n:ℝ)+1)
           + (n : ℝ) * (entropyByCount (typeCount b) n / Real.log 2) + c_dec
   ```
   `condComplexity_block_typical_le`(`EntropyRate.lean:418–495`)から **450–452 行の typicality step を除去**し
   `Hε` を `entropyByCount (typeCount b) n` に置換するだけ。`c_dec = b_c + framing_overhead`。**新規数学ゼロ、既存証明の
   コピー refactor**。落とし穴: `Hε` の `positivity`(hHε_nn)は `entropyByCount ≥ 0` が要る — Bool では
   `binEntropy_nonneg` 経由、一般 α では別途 `entropyByCount_nonneg`(既存か要確認)。
   ※ measure-free 化のため α 一般でなく **α = Bool 固定**で書くと `μ`/`Xs` 依存を切れて最短。

2. **Bool 橋 `entropyByCount = binEntropy`** ~15–25 行
   ```lean
   theorem entropyByCount_bool_eq_binEntropy {n : ℕ} (b : Fin n → Bool) (hn : 0 < n) :
       entropyByCount (typeCount b) n = Real.binEntropy ((typeCount b true : ℝ) / n)
   ```
   `unfold entropyByCount` → `Fintype.sum_bool` → `c false = n - c true`(`sum_typeCount`)→ `binEntropy` の
   `-p log p - (1-p) log(1-p)` 形へ代数。落とし穴: `Real.log x⁻¹ = - Real.log x`(`Real.log_inv`)の向き、n=0 退化。

3. **解析核「H(p) ≥ log2 - o(1) ⟹ p → 1/2」(contrapositive の fixed gap)** ~40–70 行
   `|p - 1/2| ≥ δ ⟹ binEntropy p ≤ binEntropy (1/2 - δ) < log 2`、`γ(δ) := log 2 - binEntropy(1/2-δ) > 0` を
   固定して使う。道具は §解析テーブル(`binEntropy_strictMonoOn` / `binEntropy_strictAntiOn` /
   `binEntropy_two_inv_add`(対称)/ `binEntropy_lt_log_two`)。**P6 の最難所**(唯一 stall 得る箇所、retreat 対象)。
   落とし穴: `p ∈ [0,1]` の range 確認(`typeCount ≤ n` から `p ∈ [0,1]`)、δ が `1/2` を超える端の場合分け。

4. **非圧縮列の存在(補助、`condIncompressible_count` 消費)** ~15–30 行
   `#{x | condComplexity x n < n} < 2^n` かつ length-n Bool 列は `encodeBlock` で [0,2^n) に単射 ⟹ ∃ 非圧縮 b。
   主定理(∀ 形)には不要だが、「非圧縮列が実在し頻度が 1/2」の存在言明を添える場合に。

5. **文言確定 + 極限/eventually 組立** ~40–80 行
   `∀ᶠ n, ∀ b 非圧縮, |p - 1/2| < δ` の filter 組立。`framing_overhead_eventually`(P4 既存、`o(1)/n → 0`)を流用。

**合計見積**: ~150–250 行。親 plan の「80–150 行」よりやや上振れ(解析核 3 と Bool 橋 2 が追加分)。

---

## Mathlib 壁の列挙(`@residual(wall:…)` 候補)

**P6 に genuine な Mathlib 壁は無い。** item B は「不在だが in-project 代替あり」、item A/C は「不要」。

- **(非壁・in-project 代替あり)item B の直接 lemma `C(n,k) ≤ 2^{n·H(k/n)}`**:
  - loogle `Nat.choose, Real.binEntropy` → **`Found 0 declarations mentioning Nat.choose and Real.binEntropy.`**
  - loogle `Real.binEntropy`(全 28 件)→ 全て `Mathlib.Analysis.SpecialFunctions.BinaryEntropy` の解析 lemma、
    **`Nat.choose` に触れるものは 0**。
  - loogle `Nat.choose _ _ ≤ 2 ^ _` → 該当 2 件 = `Nat.choose_le_two_pow` / `Nat.choose_succ_le_two_pow`
    (いずれも trivial `≤ 2^n`、集中に無力)。`Choose/Bounds.lean` 冒頭コメントが自ら
    「`n^r/r^r ≤ n.choose r ≤ e^r n^r/r^r` は将来追加したい」= **未整備を明示**。
  - **判定**: `@residual(wall:…)` は打たない。in-project 資産(§B/§D)で賄うので `plan:kolmogorov-slln` 内の通常作業。
    **共有 sorry-lemma 化は不要**(壁でないため)。
- **(不要)item C 組合せ裾 `∑_{tail} C(n,k) ≤ 2^n·(→0)`**: Mathlib は確率形 Hoeffding/Chernoff のみ
  (`measure_ge_le_exp_mul_mgf` / `measure_sum_ge_le_of_iIndepFun`)。pointwise route が回避するので壁判定不要。
- **(scope 外)第 2 波 prefix 塔**(`wall:prefix-free-tower`)は P6 と無関係。

---

## 撤退ラインへの距離

親計画 [`kolmogorov-moonshot-plan.md`](kolmogorov-moonshot-plan.md) §Phase P6 の撤退ライン:

> **stretch につき未達なら park のみ(`sorry + @residual(plan:kolmogorov-slln)`)、第 1 波の成否には影響しない。**

- **触れるか**: P6 は第 1 波背骨(P1–P5、達成済)に依存しない stretch。**発動しても第 1 波は無傷**。
- **発動見込み**: **低〜中**。crux(item B)は in-project 既存の refactor で確度が高い。**唯一の stall リスクは
  自作 3(解析核「H(p) ≥ log2 - o(1) ⟹ p → 1/2」)** — `binEntropy` の単峰性 lemma は揃っているが、
  fixed-gap の場合分け(δ が端に近い / p ∈ [0,1] の range 詰め)で行数が読みにくい。
- **提案する縮退 fallback(新規 retreat exit)**: 解析核が 1 セッションで閉じない場合、
  **主定理を弱い qualitative 形にせず**、per-string 上界(自作 1)+ Bool 橋(自作 2)を proof-done で確定し、
  **解析 sub-lemma 1 本だけ** `sorry + @residual(plan:kolmogorov-slln)` で park する
  (`incompressible_freq_tendsto_half` 本体はこの解析核を consume する形にして、park は解析核に局所化)。
  **hypothesis bundling 禁止**(`IsConcentrationHypothesis` 等に「H→1/2」を畳んで通したことにするのは load-bearing = 禁止)。
  raw 上界と Bool 橋は measure-free で独立に proof-done にできるので、**部分勝利(上界機械の再利用実証)**は確保できる。

---

## 着手のための skeleton

`InformationTheory/Shannon/Kolmogorov/Incompressible.lean` の出だし(20–30 行、全 sorry は type-check-done 退避出口)。
**α = Bool 固定・measure-free** を既定とする。

```lean
import InformationTheory.Shannon.Kolmogorov.Counting          -- condIncompressible_count
import InformationTheory.Shannon.Kolmogorov.EntropyRate        -- encodeBlock, typeDecoder, exists_mem_typeDecoder_lt,
                                                               --   condComplexity_block_typical_le (refactor 元), log_two_pos
import InformationTheory.Shannon.TypeClassLowerBound           -- entropyByCount, pow_div_prod_pow_eq_exp_n_entropyByCount
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy         -- Real.binEntropy 系(単峰性)

namespace InformationTheory.Kolmogorov

open MeasureTheory Real Filter Topology InformationTheory.Shannon

/-- 経験エントロピーは Bool では二値エントロピーに一致(k = 1 の個数, p = k/n)。 -/
theorem entropyByCount_bool_eq_binEntropy {n : ℕ} (hn : 0 < n) (b : Fin n → Bool) :
    entropyByCount (typeCount b) n = Real.binEntropy ((typeCount b true : ℝ) / n) := by
  sorry  -- @residual(plan:kolmogorov-slln)  -- Fintype.sum_bool + sum_typeCount + log_inv 代数(15–25 行)

/-- raw per-string 上界(typicality なし・measure-free): C(b|n) ≤ 2·logb₂(n+1) + n·binEntropy(p)/log2 + c。 -/
theorem condComplexity_bool_block_le {n : ℕ} (hn : 0 < n) (b : Fin n → Bool) :
    ∃ c : ℝ, (condComplexity (encodeBlock n b) n : ℝ)
      ≤ (2 : ℝ) * Real.logb 2 ((n:ℝ)+1)
        + (n : ℝ) * (Real.binEntropy ((typeCount b true : ℝ) / n) / Real.log 2) + c := by
  sorry  -- @residual(plan:kolmogorov-slln)  -- condComplexity_block_typical_le の refactor(typicality 除去)+ 上の橋

/-- 解析核(fixed gap): |p - 1/2| ≥ δ ⟹ binEntropy p ≤ log 2 - γ(δ), γ(δ) > 0。 -/
theorem binEntropy_gap_of_far_from_half {p δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hδ : 0 < δ) (hfar : δ ≤ |p - 2⁻¹|) :
    Real.binEntropy p ≤ Real.log 2 - (Real.log 2 - Real.binEntropy (2⁻¹ - δ)) := by
  sorry  -- @residual(plan:kolmogorov-slln)  -- binEntropy_strictMonoOn/strictAntiOn/two_inv_add(最難所・retreat 対象)

/-- CT 14.5.1: 非圧縮な Bool 列の 1 の頻度は 1/2 に収束(δ-近傍形)。 -/
theorem incompressible_freq_tendsto_half {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ b : Fin n → Bool,
      (n : ℝ) ≤ (condComplexity (encodeBlock n b) n : ℝ) →
        |((typeCount b true : ℝ) / n) - 2⁻¹| < δ := by
  sorry  -- @residual(plan:kolmogorov-slln)  -- 上 3 本 + framing_overhead_eventually で eventually 組立

end InformationTheory.Kolmogorov
```

最初に割るのは `entropyByCount_bool_eq_binEntropy`(橋、独立)と `condComplexity_bool_block_le`(refactor、既存証明を移植)。
両者 measure-free で独立に proof-done 可能。`binEntropy_gap_of_far_from_half`(解析核)が唯一の retreat 候補。

---

## 検証コマンド(settled facts 候補、confidence = loogle-neg / in-project-Read)

- item B 不在: `./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Nat.choose, Real.binEntropy"` → `Found 0`。
- item B 代替の実体: `EntropyRate.lean:445–452` を Read(`typeClassByCount_card_le` + `pow_div_prod_pow_eq_exp_n_entropyByCount` の鎖)。
- counting core: `Counting.lean:176`(`condIncompressible_count`、`@audit:ok`)。
- Bool 橋の数値確認: `entropyByCount c n = -∑_{a:Bool}(c a/n)log(c a/n)`、`c true=k, c false=n-k` ⟹ `binEntropy(k/n)`
  (`binEntropy_two_inv : binEntropy 2⁻¹ = log 2` と整合、両者 nat 基底)。

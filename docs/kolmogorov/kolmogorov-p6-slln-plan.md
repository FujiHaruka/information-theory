# Ch.14 Kolmogorov: Phase P6 非圧縮列の SLLN サブ計画

> **Parent**: [`kolmogorov-moonshot-plan.md`](kolmogorov-moonshot-plan.md) §Phase P6 (stretch)
> **Inventory (SoT for the lemma chain)**: [`kolmogorov-p6-inventory.md`](kolmogorov-p6-inventory.md)
> **Goal**: CT 2nd ed **Thm 14.5.1** — 非圧縮な長さ `n` の二値列 (`n ≤ C(encodeBlock n b | n)`) の 1 の頻度
> `typeCount b true / n` は `n → ∞` で `1/2` に収束する。新規ファイル `Incompressible.lean`。

## 進捗

- [x] M0 API 在庫調査 ✅ → [`kolmogorov-p6-inventory.md`](kolmogorov-p6-inventory.md) (item B は Mathlib 不在だが in-project 資産で代替、genuine 壁なし)
- [ ] skeleton (下 §Skeleton、全 sorry で type-check done 退避) 📋
- [ ] L1 Bool 橋 `entropyByCount_bool_eq_binEntropy` 📋
- [ ] L2 raw per-string 上界 `condComplexity_bool_block_le` (measure-free) 📋
- [ ] L3 解析核 `binEntropy_gap_of_far_from_half` 📋 ← **唯一の retreat 対象**
- [ ] L4 非圧縮列の存在 `exists_incompressible_bool_seq` 📋
- [ ] L5 primary headline `incompressible_freq_near_half` (`@[entry_point]`) 📋
- [ ] L6 Tendsto corollary `incompressible_seq_freq_tendsto_half` (`@[entry_point]`) 📋

**親同期メモ**: 本子計画の着手で親 §進捗 (DAG) の P6 行を 📋→🚧、§Sub-plan 一覧に本ファイルの backlink 行を追加する
(child が SoT、orchestrator が親を同期)。

---

## ゴール / Approach

### 主定理の形 (決着: make-or-break)

**primary headline = uniform δ-近傍 (eventually) 形** を `@[entry_point]` に据え、**Tendsto は corollary**。

```lean
/-- CT 14.5.1: 非圧縮な二値列の 1 の頻度は 1/2 に集中する (δ-近傍・eventually 形)。 -/
@[entry_point]
theorem incompressible_freq_near_half {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ b : Fin n → Bool,
      (n : ℝ) ≤ (condComplexity (encodeBlock n b) n : ℝ) →
        |((typeCount b true : ℝ) / n) - 2⁻¹| < δ
```

```lean
/-- SLLN 風 corollary: 各 n で非圧縮な列の族に沿って頻度が 1/2 に収束する。 -/
@[entry_point]
theorem incompressible_seq_freq_tendsto_half
    (w : (n : ℕ) → Fin n → Bool)
    (hw : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ (condComplexity (encodeBlock n (w n)) n : ℝ)) :
    Tendsto (fun n : ℕ ↦ (typeCount (w n) true : ℝ) / n) atTop (𝓝 2⁻¹)
```

**なぜ δ-近傍形を primary にするか (判断ログ #1 の根拠)**: `incompressible_freq_near_half` は Tendsto の ε-δ 展開そのもので、
しかも「その n の全非圧縮列 b について一様」という **数学的核** を保持する。Tendsto 単体だと族 `w` に依存し核が薄まる。
δ-近傍形なら Tendsto を機械的に導ける (L6、~15-25 行、`Metric.tendsto_atTop` / `hw` と `filter_upwards`)。

**δ(n) の明示形は作らない (判断ログ #4)**: Mathlib は `strictConcave_binEntropy` (凹性) と `binEntropy_strictMonoOn`/
`binEntropy_strictAntiOn` を持つが、**`1 - binEntropy p ≥ c·(p-1/2)²` 型の明示二次下界は不在** (verbatim 確認済、下 §Settled)。
明示 δ(n) を出すには 1/2 での二次テイラー自作 (~40-80 行) が要り、しかも headline には不要。**固定 gap の contrapositive**
(下 L3) なら二次下界ゼロで `∀ δ, eventually` を出せる — これが δ(n) 明示形の代替であり、Tendsto と等価。

### 表現の選択 (verbatim 確認済)

- **列**: `b : Fin n → Bool`。`encodeBlock n b` で ℕ 化 (`encodeBlock` = 底 `card Bool = 2` の little-endian numeral、
  `EntropyRate.lean:63`、verbatim 確認)。条件 `y = n`。⟹ `condComplexity (encodeBlock n b) n : ℕ` が型検査を通る
  (`condComplexity (x y : ℕ) : ℕ`、`UniversalMachine.lean:102`)。
- **頻度**: `p := (typeCount b true : ℝ) / n` (`typeCount b true` = b の 1 の個数、`Sanov/Basic.lean:53`)。
- **非圧縮性**: `(n : ℝ) ≤ (condComplexity (encodeBlock n b) n : ℝ)` (bit 基底で長さ ≥ n)。
- **decoder 機構の適合 (verbatim 確認)**: `exists_mem_typeDecoder_lt` (`EntropyRate.lean:311`) の結論は
  `∃ m, encodeBlock n b ∈ typeDecoder m n ∧ m < (n+1)^(Fintype.card α) * |T_c|`。α = Bool ⟹ `(n+1)^2 · |T_c|`。
  P6 の raw 上界 (L2) はこれを `invariance` に食わせる P4 上界と同じ機構を **typicality を落として** 再利用する。

### 証明の 3 段の鎖 (per-string 上界 → H 下界 → 頻度集中)

1. **(L2) raw per-string 上界 (measure-free)**: 任意 b で
   `C(encodeBlock n b | n) ≤ 2·logb 2 (n+1) + n·binEntropy(p)/log2 + c`。
   `condComplexity_block_typical_le` (`EntropyRate.lean:418-495`) の証明を **450-452 行 (typicality step
   `entropyByCount_le_of_strongTypical`) だけ除去** し、`Hε` を `binEntropy(p)` に置換した copy-refactor。
2. **非圧縮性 + L2 の合成**: `n ≤ 2·logb 2(n+1) + n·binEntropy(p)/log2 + c` ⟹
   `binEntropy(p) ≥ log2 · (1 - (2·logb 2(n+1) + c)/n) = log2 - o(1)`。
3. **(L3) contrapositive の解析核 (固定 gap)**: `|p - 1/2| ≥ δ` ⟹ `binEntropy(p) ≤ binEntropy(1/2 - δ) < log2`。
   `γ(δ) := log2 - binEntropy(2⁻¹ - δ) > 0` (固定正定数)。o(1) が eventually `γ(δ)` を下回る ⟹ 非圧縮なら `|p-1/2| < δ`。

### 実装原則

- **measure-free 死守**: P6 は P4 の `μ`/`Xs`/i.i.d. (`iIndepFun`+`Pairwise ⟂`+`IdentDistrib`) を **一切継承しない**
  (inventory 中核所見)。継承すると load-bearing でない冗長結合になる。全補題は α = Bool 固定 + 純組合せ的資産のみ消費。
- **Skeleton-driven**: 下 §Skeleton を全 sorry で Write → type-check done 確認 → L1/L2/L4 (相互独立・measure-free) を
  先に proof-done → L3 (最難所) → L5/L6 (L2/L3 を消費)。
- **shared-lemma 署名変更なし ⟹ consumer ripple 解析 (dep_consumers) 不要**: L2 は既存 `condComplexity_block_typical_le`
  の **新規 copy** (`condComplexity_bool_block_le`) であって署名変更ではない。既存資産 (`invariance` /
  `exists_mem_typeDecoder_lt` / `typeClassByCount_card_le` / `pow_div_prod_pow_eq_exp_n_entropyByCount` /
  `condIncompressible_count` / binEntropy 群) はすべて read-only 消費。

---

## Per-decl 分解 (skeleton-first、依存資産 file:line + 見積行数)

各 `proof-log`: **no** (親 P6 = stretch、metrics 取得対象外)。

| # | 宣言 (署名要点) | 消費する既存資産 `file:line` | 見積 | risk |
|---|---|---|---|---|
| **L1** | `entropyByCount_bool_eq_binEntropy {n} (hn : 0 < n) (b : Fin n → Bool) : entropyByCount (typeCount b) n = Real.binEntropy ((typeCount b true : ℝ)/n)` | `entropyByCount` (`TypeClassLowerBound.lean:38`) / `Fintype.sum_bool` / `sum_typeCount` (Sanov) / `Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub` (`BinaryEntropy.lean:71`) | 15-25 | 低 |
| **L2** | `condComplexity_bool_block_le : ∃ c : ℝ, 0 ≤ c ∧ ∀ {n} (hn : 0 < n) (b : Fin n → Bool), (condComplexity (encodeBlock n b) n : ℝ) ≤ 2 * Real.logb 2 ((n:ℝ)+1) + (n:ℝ) * (Real.binEntropy ((typeCount b true:ℝ)/n) / Real.log 2) + c` | copy-refactor of `condComplexity_block_typical_le` (`EntropyRate.lean:418-495`)。`invariance`/`typeDecoder_partrec`/`exists_mem_typeDecoder_lt` (`:311`)/`typeClassByCount_card_le` (`MultinomialLowerBound.lean:677`)/`pow_div_prod_pow_eq_exp_n_entropyByCount` (`TypeClassLowerBound.lean:55`)/`natLen_le`/`natLen_le_of_lt_two_pow` (`UniversalMachine.lean:89`)/L1/`Real.binEntropy_nonneg` (`BinaryEntropy.lean:93`) | 40-60 | 低-中 |
| **L3** | `binEntropy_gap_of_far_from_half {p δ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 2⁻¹) (hfar : δ ≤ \|p - 2⁻¹\|) : Real.binEntropy p ≤ Real.binEntropy (2⁻¹ - δ)` | `binEntropy_strictMonoOn` (`:422`, `.monotoneOn`)/`binEntropy_one_sub` (`:79`)/`binEntropy_lt_log_two` (`:139`) | 40-70 | **高 (唯一 stall 得る)** |
| **L4** | `exists_incompressible_bool_seq : ∃ w : (n:ℕ) → Fin n → Bool, ∀ n, 0 < n → (n:ℝ) ≤ (condComplexity (encodeBlock n (w n)) n : ℝ)` | `condIncompressible_count` (`Counting.lean:176`, `@audit:ok`)/`encodeBlock_injective` (`EntropyRate.lean:67`)/`encodeBlock_lt` (`:75`)/`Set.ncard_le_ncard` | 20-35 | 低-中 |
| **L5** | `incompressible_freq_near_half {δ} (hδ : 0 < δ)` (§ゴール、`@[entry_point]`) | L2 + L3 + `framing_overhead_eventually` (`EntropyRate.lean:353`) + `log_two_pos` (`:89`) + `sum_typeCount` (`p ∈ [0,1]`) | 40-70 | 中 (filter 組立 + δ>2⁻¹ の自明分岐) |
| **L6** | `incompressible_seq_freq_tendsto_half (w) (hw)` (§ゴール、`@[entry_point]`) | L5 + `Metric.tendsto_atTop` (or `NormedAddCommGroup.tendsto_nhds`)/`Filter.Eventually.mono` | 15-25 | 低 |

**合計 ~170-285 行** (inventory の ~150-250 と整合、上振れは L3 の場合分けと L5 の filter 組立)。

### L2 refactor の要点 (既存証明のどこを切るか)

`condComplexity_block_typical_le` の proof body で **typicality 依存は line 450-452 の
`entropyByCount_le_of_strongTypical` 1 箇所のみ**。L2 では:
- `hTc_exp` (line 445-452) を **`|T_c| ≤ exp(n · entropyByCount (typeCount b) n)`** で止める
  (`typeClassByCount_card_le` + `pow_div_prod_pow_eq_exp_n_entropyByCount` だけ、`entropyByCount_le_of_strongTypical`
  への `.trans` を除去)。
- 以降の `natLen` 上界 / `logb` 連鎖 (line 456-495) は `Hε` を `entropyByCount (typeCount b) n` に読み替えてそのまま。
- **nonneg step**: 旧 `hHε_nn : 0 ≤ Hε` (positivity) に相当する `0 ≤ entropyByCount (typeCount b) n` は、in-project に
  `entropyByCount_nonneg` が **無い** (grep 確認) ため、**L1 で `= binEntropy(p)` に橋渡し後 `Real.binEntropy_nonneg`
  (`p ∈ [0,1]`) で出す**。⟹ L2 は Bool 固定で書くのが最短 (μ/Xs も切れる)。
- 最終式の `entropyByCount (typeCount b) n` を L1 で `Real.binEntropy (p)` に置換して署名の形にする。

### L3 の証明構造 (最難所)

`hfar : δ ≤ |p - 2⁻¹|` ⟹ `p ≤ 2⁻¹ - δ` または `p ≥ 2⁻¹ + δ` (abs 場合分け):
- `p ≤ 2⁻¹ - δ`: `p, 2⁻¹-δ ∈ Icc 0 2⁻¹` (`hp0`, `hδ1`) ⟹ `binEntropy_strictMonoOn.monotoneOn` で
  `binEntropy p ≤ binEntropy (2⁻¹ - δ)`。
- `p ≥ 2⁻¹ + δ`: `1 - p ≤ 2⁻¹ - δ` かつ `1 - p ≥ 0` (`hp1`) ⟹ 前ケースを `1-p` に適用 +
  `binEntropy_one_sub : binEntropy (1-p) = binEntropy p`。
- 落とし穴: `2⁻¹ - δ ≥ 0` は `hδ1 : δ ≤ 2⁻¹` が保証。`Icc` メンバシップ整形 (`Set.mem_Icc`)。
- headline 側 (L5) で `γ(δ) := log2 - binEntropy(2⁻¹-δ)` を `binEntropy_lt_log_two.2 (show 2⁻¹-δ ≠ 2⁻¹ from ...)`
  で `> 0` に。**`δ ≤ 2⁻¹` の仮定は L5 で δ>2⁻¹ を自明分岐 (|p-1/2| ≤ 1/2 < δ) に落として供給。**

---

## 撤退ライン (park slug = `kolmogorov-slln`)

親 §Phase P6 の撤退: **stretch につき未達なら park のみ、第 1 波 (P1-P5、達成済) の成否に無影響。**

- **発動見込み: 低-中。** crux (L2) は in-project 既存 refactor で確度が高い。**唯一の stall 候補 = L3 (解析核)** の
  固定-gap 場合分け (δ が `1/2` 端に近い / `Icc` range 詰め)。
- **park 発動時の局所化 (部分勝利を確保)**: L3 が 1 セッションで閉じない場合、**L3 の body のみ**
  `sorry  -- @residual(plan:kolmogorov-slln)` で park する。L1 / L2 / L4 は measure-free・相互独立で **proof-done を
  確定** (raw 上界機械の再利用実証 = 部分勝利)。L5 / L6 は L3 を **consume** するので sorryAx が伝播するが、
  body 自体は honest な組立 (L3 呼び出し) のまま — 残 residual は L3 の 1 slug に局所化される。
- **禁止 (honesty)**: 「H → 1/2」を `IsConcentrationHypothesis` 等の load-bearing predicate に畳んで L5 を「通った
  ことにする」のは bundling = 禁止 (CLAUDE.md 検証の誠実性)。撤退は必ず L3 の body sorry で。
- **wall 判定なし**: item B (`C(n,k) ≤ 2^{n·H(k/n)}`) は Mathlib 不在だが in-project 資産で代替 ⟹ `@residual(wall:…)` は
  打たない。共有 sorry-lemma 化も不要。

---

## Skeleton (`Incompressible.lean` 出だし、全 sorry = type-check done 退避出口)

```lean
import InformationTheory.Shannon.Kolmogorov.Counting          -- condIncompressible_count
import InformationTheory.Shannon.Kolmogorov.EntropyRate        -- encodeBlock, exists_mem_typeDecoder_lt,
                                                               --   condComplexity_block_typical_le (refactor 元),
                                                               --   framing_overhead_eventually, log_two_pos
import InformationTheory.Shannon.TypeClassLowerBound           -- entropyByCount, pow_div_prod_pow_eq_exp_n_entropyByCount
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy         -- Real.binEntropy 群

namespace InformationTheory.Kolmogorov

open MeasureTheory Real Filter Topology InformationTheory.Shannon

theorem entropyByCount_bool_eq_binEntropy {n : ℕ} (hn : 0 < n) (b : Fin n → Bool) :
    entropyByCount (typeCount b) n = Real.binEntropy ((typeCount b true : ℝ) / n) := by
  sorry  -- @residual(plan:kolmogorov-slln)  -- L1: Fintype.sum_bool + sum_typeCount + negMulLog 橋

theorem condComplexity_bool_block_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {n : ℕ} (_ : 0 < n) (b : Fin n → Bool),
      (condComplexity (encodeBlock n b) n : ℝ)
        ≤ 2 * Real.logb 2 ((n : ℝ) + 1)
          + (n : ℝ) * (Real.binEntropy ((typeCount b true : ℝ) / n) / Real.log 2) + c := by
  sorry  -- @residual(plan:kolmogorov-slln)  -- L2: condComplexity_block_typical_le の typicality 除去 refactor + L1

theorem binEntropy_gap_of_far_from_half {p δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 2⁻¹) (hfar : δ ≤ |p - 2⁻¹|) :
    Real.binEntropy p ≤ Real.binEntropy (2⁻¹ - δ) := by
  sorry  -- @residual(plan:kolmogorov-slln)  -- L3: strictMonoOn + binEntropy_one_sub (retreat 対象)

theorem exists_incompressible_bool_seq :
    ∃ w : (n : ℕ) → Fin n → Bool,
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ (condComplexity (encodeBlock n (w n)) n : ℝ) := by
  sorry  -- @residual(plan:kolmogorov-slln)  -- L4: condIncompressible_count + encodeBlock 単射

@[entry_point]
theorem incompressible_freq_near_half {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ b : Fin n → Bool,
      (n : ℝ) ≤ (condComplexity (encodeBlock n b) n : ℝ) →
        |((typeCount b true : ℝ) / n) - 2⁻¹| < δ := by
  sorry  -- @residual(plan:kolmogorov-slln)  -- L5: L2 + L3 + framing_overhead_eventually

@[entry_point]
theorem incompressible_seq_freq_tendsto_half
    (w : (n : ℕ) → Fin n → Bool)
    (hw : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ (condComplexity (encodeBlock n (w n)) n : ℝ)) :
    Tendsto (fun n : ℕ ↦ (typeCount (w n) true : ℝ) / n) atTop (𝓝 2⁻¹) := by
  sorry  -- @residual(plan:kolmogorov-slln)  -- L6: L5 を Metric.tendsto_atTop で Tendsto 化

end InformationTheory.Kolmogorov
```

**最初に割る順**: L1 (橋、独立) → L2 (refactor、既存証明移植) → L4 (存在、独立) → L3 (解析核) → L5 → L6。
L1/L2/L4 は measure-free で相互独立に proof-done 可能。`Incompressible.lean` 追加後 `InformationTheory.lean` に import 登録。

---

## Settled facts (confidence 付き、再検証コマンド)

- **item B (`C(n,k) ≤ 2^{n·H(k/n)}`) は Mathlib 直接 lemma 不在、in-project 代替あり** (confidence = `loogle-neg`):
  `loogle "Nat.choose, Real.binEntropy"` → **Found 0**。代替 = `typeClassByCount_card_le` ∘
  `pow_div_prod_pow_eq_exp_n_entropyByCount` (一般 α で `|T_c| ≤ exp(n·entropyByCount c n)`)。壁ではない。
- **明示二次下界 `1-binEntropy p ≥ c(p-1/2)²` は Mathlib 不在** (confidence = `machine`、`BinaryEntropy.lean` grep):
  在るのは `strictConcave_binEntropy` (`:443` StrictConcaveOn) / `binEntropy_strictMonoOn` (`:422`) /
  `binEntropy_strictAntiOn` (`:427`) / `binEntropy_lt_log_two` (`:139`) / `binEntropy_two_inv` (`:69`) /
  `binEntropy_one_sub` (`:79`) / `binEntropy_nonneg` (`:93`)。⟹ 固定-gap route (L3) を採り明示 δ(n) は作らない。
- **in-project に `entropyByCount_nonneg` 無し** (confidence = `machine`、`rg` 確認): L2 の nonneg step は L1 橋 +
  `Real.binEntropy_nonneg` で出す (Bool 固定の追加理由)。

## 判断ログ

1. **primary headline = δ-近傍 (eventually) 形、Tendsto は corollary**: `incompressible_freq_near_half` が数学的核
   (その n の全非圧縮列で一様) を保持。Mathlib に二次下界が無く明示 δ(n) を作れないため、固定-gap の
   `∀ δ, eventually` 形が最短で、Tendsto (L6) を機械的に含意する。
2. **表現 = `b : Fin n → Bool` / `encodeBlock n b` / 条件 `n` / 頻度 `typeCount b true / n`**: `encodeBlock` (`:63`) と
   `exists_mem_typeDecoder_lt` (`:311`、Bool で `m < (n+1)²·|T_c|`) を verbatim 確認、P4 上界機構がそのまま適合。
3. **measure-free 死守**: P6 は μ/Xs/i.i.d. を継承しない (inventory 中核所見)。L2 は既存
   `condComplexity_block_typical_le` の **新規 copy** (署名変更でない) ⟹ consumer ripple 解析不要、全資産 read-only 消費。
4. **δ(n) 明示形は作らない**: `strictConcave_binEntropy` はあるが `1-binEntropy p ≥ c(p-1/2)²` 型は不在
   (§Settled)。固定-gap contrapositive (L3) で回避。

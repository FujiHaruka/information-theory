# Ch.14 Kolmogorov 複雑性 第 2 波 (prefix 塔) — Mathlib API 在庫調査

> **Status**: INVENTORY (2026-07-25)。第 2 波 (prefix 複雑性 K / 普遍確率 P_U / Chaitin Ω / 十分統計量、
> P7–P10) の moonshot 立案前台帳。
> **親**: [`kolmogorov-scouting.md`](kolmogorov-scouting.md) §0/§1/§3 (山場マップ + 「唯一の genuine 壁 = prefix 塔」判定)、
> [`kolmogorov-moonshot-plan.md`](kolmogorov-moonshot-plan.md) (第 1 波背骨、全 proof-done、§Out で第 2 波を隔離)。
> **重複回避**: 意味論層 (`Code`/`eval`/`evaln`/`exists_code`/`smn`/`encodeCode`/停止問題/符号化) は
> [`kolmogorov-mathlib-inventory.md`](kolmogorov-mathlib-inventory.md) が SoT。本台帳は **相互参照のみ**で再掲しない。
> 全 `file:line` は `.lake/packages/mathlib/` 実体を Read して確認済み。loogle は `Found N` を verbatim 記録。

## 一行サマリ

**scouting §0/§3 の「prefix-free 機械 / 自己限定符号 / program 上の Kraft = 完全に不在」は overturn される。**
Mathlib は **一意復号可能符号 `UniquelyDecodable` の定義 + 有限符号版 Kraft-McMillan 不等式
`∑ 2^{-|w|} ≤ 1` を既に持つ** (`Mathlib/InformationTheory/Coding/`、2026 追加)。この「本章唯一の解析の壁」と
名指しされていた Kraft の解析核が既存であり、しかも `summable_of_sum_le` (有限部分和 ≤ c ⟹ Summable) が
**無限プログラム集合上の Ω 収束への橋そのもの** として存在する。⟹ **P9 Ω の well-defined 性 (収束) は壁でなく
plumbing に縮む。** 残る「不在」は (a) prefix-free 述語そのもの (Found 0、`List.IsPrefix` から数行で自作)、
(b) prefix 機械 U_prefix / K / P_U / Ω / Martin-Löf randomness / 十分統計量 の**定義群**であり、これらは
「解析の壁 (hard)」ではなく「新規定義の選択 (big)」。**第 2 波に genuine な解析壁は残っていない。**

- **既存 (解析エンジン)**: Kraft-McMillan (有限 UD 符号) / `summable_of_sum_le` / `ENNReal.tsum`(常時定義) /
  `ENNReal.log` (EReal 値) / `Real.logb` / `List.IsPrefix` / `Fintype.card Bool = 2` = **100% 既存**。
- **自作 (定義層)**: prefix-free 述語 + prefix ⟹ UD 橋 + U_prefix + K + P_U + Ω + (ML-randomness) + KSS = **0% 既存**
  (新理論なので当然、ただし解析壁なし)。
- **P7–P10 再評価**: P7 △→**○** (Kraft + summable で下界が組める)、P8 ✖→**△** (等号方向は依然 crux だが
  Kraft 既存で片側は軽い)、P9 ✖→**○〜△** (Ω 収束は Kraft+summable で解決、非計算性は第 1 波 halting 再利用)、
  P10 ✖→✖ (据え置き、解析壁ではなく定義量が多い)。

---

## 主定理の最終形 (prefix 塔の頂点 = P8 Levin 符号化定理)

第 2 波は単一主定理でなく P7→P8→P9→(P10) の塔。頂点 P8 (Levin) を headline に据える (番号 CT 2nd ed §14.6 は
PDF 未収蔵につき着手前に verbatim 確認)。以下は **pivot 前の設計形** (定義は Mathlib-shape-driven で確定させる)。

```lean
-- prefix 機械 U_prefix の domain は prefix-free (自己限定)。
-- prefixComplexity K(x) = min { |p| | U_prefix p = x }、universalProb P_U(x) = ∑_{U_prefix p = x} 2^{-|p|}。
theorem levin_coding_theorem :        -- @[entry_point] 予定、CT §14.6
    ∃ c : ℕ, ∀ x : ℕ,
      |(-(Real.logb 2 (universalProb x))) - (prefixComplexity x : ℝ)| ≤ c
```

証明戦略 (6–10 行 pseudo-Lean):

```
-- (≤ 方向 = P7 普遍確率下界、Kraft 既存で軽い):
--   最短 prefix program p* (長さ K(x)) が U_prefix で x を出す ⟹ P_U(x) ≥ 2^{-K(x)}
--   ⟹ -log₂ P_U(x) ≤ K(x)                                      -- ENNReal.le_tsum / sum_le_tsum の 1 項下界
P_U(x) ≥ 2^{-K(x)}  ⟹  -log P_U(x) ≤ K(x)                        -- ← P7、片側は下界 1 項で出る
-- (≥ 方向 = 等号 crux、Levin 本体):
--   P_U を prefix-free 復号器で「符号長 ≈ -log P_U(x) の program」に再構成 (Shannon-Fano-Elias/算術符号)
--   ⟹ K(x) ≤ -log₂ P_U(x) + c                                  -- ← P8 crux、prefix program の構成が要
K(x) ≤ -log P_U(x) + c                                           -- ← 等号方向、self-build の山
-- 合流:
|K(x) + log₂ P_U(x)| ≤ c                                         -- 両側を束ねる
```

**核心の依存**: (≤) は **P_U の 1 項下界** (`ENNReal.le_tsum`) と Kraft の well-defined 性 (既存) で軽い。
(≥) は **P_U の質量から prefix program を構成する符号化** = 第 2 波最大の self-build (Kraft は使うが逆向き構成)。

---

## API 在庫テーブル

status 凡例: ✅ 既存 / ⚠️ 既存だが噛み合わせ注意 / ❌ 不在 (自作)。`[...]` 型クラス前提・結論形は **verbatim**。

### §A. 解析エンジン — 「唯一の壁」と名指しされた Kraft が既存 (最重要の overturn)

| 概念 | Mathlib API (verbatim signature) | file:line | status | 第 2 波での扱い |
|---|---|---|---|---|
| **一意復号可能符号 (定義)** | `def UniquelyDecodable (S : Set (List α)) : Prop := ∀ (L₁ L₂ : List (List α)), (∀ w ∈ L₁, w ∈ S) → (∀ w ∈ L₂, w ∈ S) → L₁.flatten = L₂.flatten → L₁ = L₂` | `Mathlib/InformationTheory/Coding/UniquelyDecodable.lean:35` | ✅ | prefix-free ⟹ UD の受け皿。Ω 収束の hypothesis 型 |
| **Kraft-McMillan 不等式** | `theorem kraft_mcmillan_inequality {S : Finset (List α)} [Fintype α] [Nonempty α] (h : UniquelyDecodable (S : Set (List α))) : ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1` | `Mathlib/InformationTheory/Coding/KraftMcMillan.lean:149` | ⚠️ | **`S : Finset` (有限符号) が必須** — Ω は無限 program 集合なので **有限部分集合ごとに適用 + `summable_of_sum_le`** で無限化する (§Key-preconditions) |
| UD 空文字列排除 | `lemma UniquelyDecodable.epsilon_not_mem (h : UniquelyDecodable S) : [] ∉ S` | `Coding/UniquelyDecodable.lean:46` | ✅ | prefix 機械の空 program 排除に |
| UD flatten 単射 | `lemma UniquelyDecodable.flatten_injective (h : UniquelyDecodable S) : Function.Injective (fun (L : {L : List (List α) // ∀ x ∈ L, x ∈ S}) => L.val.flatten)` | `Coding/UniquelyDecodable.lean:51` | ✅ | 一意復号の実体 |
| **有限和 ≤ c ⟹ Summable** | `theorem summable_of_sum_le {ι : Type*} {f : ι → ℝ} {c : ℝ} (hf : 0 ≤ f) (h : ∀ u : Finset ι, ∑ x ∈ u, f x ≤ c) : Summable f` | `Mathlib/Topology/Algebra/InfiniteSum/Real.lean:84` | ✅ | **Kraft (有限) → Ω (無限) の橋**。`c = 1`、`f p = 2^{-|p|}` |
| range 版 | `theorem summable_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n) (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : Summable f` | `InfiniteSum/Real.lean:89` | ✅ | program を ℕ 列挙する場合の別形 |

> **overturn の要点**: scouting §0「prefix-free 機械 / Kraft on programs = 完全に不在」「本章唯一の genuine
> 解析/量の壁」は **Kraft の解析核については誤り**。`Mathlib/InformationTheory/Coding/` (Elazar Gershuni, 2026)
> が UD 符号の Kraft-McMillan を証明済み。**「program 上の Kraft」に特化した形は無い**が、それは
> `α = Bool` を代入し program 集合の UD 性を渡すだけの plumbing であって解析ではない。CLAUDE.md
> 「Search in-project before concluding absent」の Mathlib 版事故 (loogle 語が狭くて既存資産を見落とす) を
> 回避できた事例。

### §B. 可算和 / 収束インフラ (Ω = ∑ 2^{-|p|} の well-defined 性)

| 概念 | Mathlib API (verbatim signature) | file:line | status | 第 2 波での扱い |
|---|---|---|---|---|
| ℝ≥0∞ の tsum は常時定義 | `protected theorem ENNReal.tsum_eq_iSup_sum {f : α → ℝ≥0∞} : ∑' a, f a = ⨆ s : Finset α, ∑ a ∈ s, f a` | `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean:71` | ✅ | **ℝ≥0∞ 版なら Summable 不要** (iSup で常に定義)。Ω を `ℝ≥0∞` で建てれば収束証明が消える |
| ℝ≥0∞ 有限和 ≤ tsum | `protected theorem ENNReal.sum_le_tsum {f : α → ℝ≥0∞} (s : Finset α) : ∑ x ∈ s, f x ≤ ∑' x, f x` | `InfiniteSum/ENNReal.lean:118` | ✅ | 有限部分和からの下界 |
| ℝ≥0∞ 1 項 ≤ tsum | `protected theorem ENNReal.le_tsum (a : α) : f a ≤ ∑' a, f a` | `InfiniteSum/ENNReal.lean:146` | ✅ | **P7 下界 `P_U(x) ≥ 2^{-K(x)}` の 1 項下界** (最短 program の寄与) |
| ℝ 版 tsum ≤ (上界) | `summable_of_sum_le` (§A) 経由で `Summable` → `tsum_le_of_sum_le` 系 | `InfiniteSum/Real.lean` | ✅ | Ω を `ℝ` で建てる場合の ≤ 1 |

> **設計判断 (Mathlib-shape-driven)**: Ω / P_U を **`ℝ≥0∞` 値** で定義すると `tsum` が常時定義 (`tsum_eq_iSup_sum`)
> で収束証明が不要、`≤ 1` は `ENNReal.sum_le_tsum` + Kraft(有限)で出る。**`ℝ` 値**にすると `summable_of_sum_le` で
> Summable を先に立てる必要がある。P8 の `-log P_U` は `ENNReal.log : ℝ≥0∞ → EReal` (§C) と型が噛むので
> **`ℝ≥0∞` 値定義を第一候補**とする (§Key-preconditions)。

### §C. 対数 (P8 の -log P_U、P7 の 2^{-K})

| 概念 | Mathlib API (verbatim signature) | file:line | status | 第 2 波での扱い |
|---|---|---|---|---|
| ℝ≥0∞ の対数 (EReal 値) | `noncomputable def ENNReal.log (x : ℝ≥0∞) : EReal := if x = 0 then ⊥ else if x = ⊤ then ⊤ else Real.log x.toReal` | `Mathlib/Analysis/SpecialFunctions/Log/ENNRealLog.lean:46` | ✅ | **P_U : ℝ≥0∞ の -log を EReal で取る**。`log_zero = ⊥` が P_U(x)=0 (記述不能) を自然に扱う |
| ℝ≥0∞ log の ofReal | `@[simp] lemma ENNReal.log_ofReal (x : ℝ) : log (ENNReal.ofReal x) = if x ≤ 0 then ⊥ else ↑(Real.log x)` | `Log/ENNRealLog.lean:58` | ✅ | ℝ 値との橋 |
| ℝ の底付き対数 | `noncomputable def Real.logb (b x : ℝ) : ℝ := log x / log b` | `Mathlib/Analysis/SpecialFunctions/Log/Base.lean:43` | ✅ | 2 進レート `-log₂ P_U`。第 1 波 P4/P6 で既に消費実績 (`Real.logb 2`) |
| Bool の濃度 = 2 | `theorem Fintype.card_bool : Fintype.card Bool = 2` | `Mathlib/Data/Fintype/Card.lean:182` | ✅ | Kraft の `D = Fintype.card α` に `α = Bool` 代入 ⟹ `2^{-|w|}` |

### §D. prefix-free 述語の構築部品 + 符号化 (Mathlib 側の素材)

| 概念 | Mathlib API (verbatim signature) | file:line | status | 第 2 波での扱い |
|---|---|---|---|---|
| リスト前置関係 | `List.IsPrefix` (`l₁ <+: l₂`)、`List.isPrefixOf` 等 449 decl | `Init/Data/List/Basic` (core) | ✅ | **`PrefixFree S := ∀ a ∈ S, ∀ b ∈ S, a <+: b → a = b` を数行で自作**する土台 |
| ℕ の 2 進符号 | `def Computability.encodeNat (n : ℕ) : List Bool` / `decodeNat` | `Mathlib/Computability/Encoding.lean:105` | ✅ | prefix program の payload 符号 (第 1 波と共有) |
| Code ≃ ℕ | `instance Nat.Partrec.Code.instDenumerable : Denumerable Code` | `Mathlib/Computability/PartrecCode.lean:176` | ✅ | prefix U_prefix の interpret モードで `eval (ofNat Code idx)` に委譲 (第 1 波と同機構) |
| 意味論層全般 | `Code`/`eval`/`exists_code`/`smn`/`evaln`/停止問題 | `PartrecCode.lean` / `Halting.lean` | ✅ | [`kolmogorov-mathlib-inventory.md`](kolmogorov-mathlib-inventory.md) §1/§2/§5 が SoT (再掲しない) |

### §E. 第 1 波からの再利用可能資産 (read-only 消費、署名 verbatim)

すべて `InformationTheory/Shannon/Kolmogorov/` に既存・proof-done。第 2 波 (prefix) は plain C の上に K を載せる設計。

| 資産 | verbatim signature | file:line | 第 2 波での役割 |
|---|---|---|---|
| plain 条件複雑性 | `noncomputable def condComplexity (x y : ℕ) : ℕ := sInf { l | ∃ p : List Bool, p.length = l ∧ x ∈ universalEval p y }` | `UniversalMachine.lean:102` | prefix K の設計雛形 (program = `List Bool`、`sInf` 到達性の型) |
| plain 複雑性 | `noncomputable def complexity (x : ℕ) : ℕ := condComplexity x 0` | `UniversalMachine.lean:106` | K ≥ C の比較対象 (prefix K は plain C の上界) |
| plain 万能機械 | `noncomputable def universalEval : List Bool → ℕ → Part ℕ` (literal / interpret 2 モード) | `UniversalMachine.lean:54` | ⚠️ **prefix-free でない** (literal `false::bs` が前置閉) ⟹ U_prefix は別構成。interpret 委譲の機構のみ再利用 |
| 不変性 (code 版) | `theorem invariance_code (c : Code) : ∃ b : ℕ, ∀ (x y : ℕ) (q : List Bool), x ∈ eval c (Nat.pair (decodeNat q) y) → condComplexity x y ≤ q.length + b` | `Invariance.lean:36` | prefix 不変性の雛形 (pointwise-over-descriptions 形、min-RHS 退化回避) |
| 不変性 (機械版) | `theorem invariance (A : ℕ → ℕ → Part ℕ) (hA : Partrec₂ A) : ∃ b : ℕ, ∀ (x y : ℕ) (q : List Bool), x ∈ A (decodeNat q) y → condComplexity x y ≤ q.length + b` | `Invariance.lean:53` | 同上 |
| 数え上げ | `theorem incompressible_count (k : ℕ) : {x : ℕ | complexity x < k}.ncard < 2 ^ k` | `Counting.lean:108` | prefix 版でも `2^k` バウンドの雛形 (K の数え上げは Kraft でより精密化可) |
| 非計算性 | `theorem complexity_not_computable : ¬ Computable complexity` | `Noncomputable.lean:83` | **Ω の非計算性 (P9) の還元先候補** (Berry / halting、第 1 波機構) |
| 非計算性 (条件版) | `theorem condComplexity_not_computable (y : ℕ) : ¬ Computable (fun x ↦ condComplexity x y)` | `Noncomputable.lean:40` | 同上 (strictly stronger) |
| エントロピー | `noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ := ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})` | `InformationTheory/Shannon/Bridge.lean:40` | P10 KSS / MDL の H(X) 項 (混在: plain C と共有) |
| 停止問題 | `theorem ComputablePred.halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom` | `Mathlib/Computability/Halting.lean:65` | P9 Ω 非計算性の背骨 (第 1 波 P5 と同弾) |

---

## Key-preconditions box (事故が起きやすい前提)

- **`kraft_mcmillan_inequality` は `S : Finset (List α)` = 有限符号が必須。** Ω / P_U の domain (停止する prefix
  program 全体) は **可算無限**。よって Kraft を**各有限部分集合 `u ⊆ (停止 program)` に適用** ⟹
  `∀ u, ∑_{w∈u} 2^{-|w|} ≤ 1` ⟹ `summable_of_sum_le` (c=1) で `Summable` / `ENNReal.tsum` の `≤ 1` に無限化する。
  「Kraft を無限集合に直接適用」はできない (型が合わない)。
- **`kraft_mcmillan_inequality` の hypothesis は `UniquelyDecodable`、prefix-free ではない。** prefix-free ⟹ UD は
  標準だが Mathlib 不在 (自作、数行、`List.IsPrefix` から)。さらに **UD の下方単調性** (`S' ⊆ S ∧ UD S ⟹ UD S'`) も
  有限部分集合への適用で要る (自作 ~5 行、UD の ∀ が部分集合で自動継承)。
- **`[Fintype α] [Nonempty α]` (Kraft の型クラス)**: `α = Bool` で自動充足 (`Fintype Bool` / `Nonempty Bool` は既存 instance)。
  だが **program alphabet を `List Bool` でなく `ℕ`-as-binary で建てると `α` が定まらず Kraft が使えない** —
  第 1 波の設計判断 (program = `List Bool`、判断ログ #2(ii)) を prefix 側も踏襲すること。
- **Ω / P_U を `ℝ` で建てるか `ℝ≥0∞` で建てるか**: `ℝ≥0∞` なら `tsum_eq_iSup_sum` で収束証明が消え、`-log` は
  `ENNReal.log : ℝ≥0∞ → EReal` と型が噛む。**`ℝ≥0∞` 値を第一候補**。ただし P8 の最終不等式 `|K + log₂ P_U| ≤ c` は
  `ℝ` の絶対値なので `EReal → ℝ` の `.toReal` 変換 (P_U(x) ∈ (0,1] で有限) が要る (plumbing、P_U(x)>0 の担保が前提)。
- **P_U(x) = 0 (記述不能な x) の境界**: `ENNReal.log 0 = ⊥`。P8 は「x が U_prefix で記述可能」= P_U(x)>0 の前提下で
  述べる (K(x) 有限 ⟺ 記述可能)。境界を落とすと `-log = ⊤` で不等式が破れる (verbatim 確認済: `log_zero = ⊥`)。

---

## 自作が必要な要素 (優先度順、壁部分)

第 2 波の未達は**すべて「定義群の self-build」**であり、解析壁は無い (Kraft が既存のため)。

1. **【最優先・foundation】prefix-free 機械 U_prefix + prefix 複雑性 K の定義**
   - **何を自作**: `PrefixFree (S : Set (List Bool)) : Prop` (述語、`List.IsPrefix` から)、prefix ⟹ UD 橋、
     U_prefix の domain が prefix-free になる 2 モード parse (self-delimiting 符号)、
     `prefixComplexity x := sInf { |p| | x ∈ U_prefix p }`、well-defined 性 (非空 ⟹ `sInf_mem`)。
   - **見積行数**: **150–300 行**。第 1 波 `UniversalMachine.lean` (108 行) の設計を踏襲できるが、literal モードを
     **prefix-free 化** (payload 長を自己限定符号で前置) するのが第 1 波にない新規分。
   - **依存 Mathlib**: `List.IsPrefix` (§D)、`Denumerable Code` (§D、interpret 委譲)、`encodeNat` (§D)。
   - **難所**: literal モードを prefix-free に保つ符号 (Elias γ / 長さ前置)。第 1 波 `literalProg = false::encodeNat x`
     は前置閉なので **そのまま使えない** (§E ⚠️)。K の数え上げは Kraft でより精密化できる。
   - **第 1 波再利用**: interpret モードの `eval (ofNat Code idx)` 委譲機構 (判断ログ #2(i)) は流用可 = 手組み回避。

2. **【P7】普遍確率 P_U : ℕ → ℝ≥0∞ の定義 + 下界 `P_U(x) ≥ 2^{-K(x)}`**
   - **何を自作**: `universalProb x := ∑' p : {p // x ∈ U_prefix p}, 2^{-p.length}` (ℝ≥0∞)、`≤ 1` (Kraft+summable)、
     下界補題 (最短 program の 1 項)。
   - **見積行数**: **60–120 行** (定義 + well-defined + 下界)。
   - **依存 Mathlib**: `ENNReal.tsum_eq_iSup_sum` / `ENNReal.le_tsum` (§B、下界 1 項)、`kraft_mcmillan_inequality` +
     `summable_of_sum_le` (§A、≤ 1)。
   - **難所**: なし (Kraft + le_tsum で片側は軽い)。P7 は scouting △ → **○ に格上げ**。

3. **【P9】Chaitin Ω の定義 + `Ω ≤ 1` + 非計算性**
   - **何を自作**: `chaitinOmega := ∑' p : {p // (U_prefix p).Dom}, 2^{-p.length}`、`≤ 1` (Kraft+summable)、
     `¬ Computable`。
   - **見積行数**: **80–150 行** (well-defined は Kraft で軽い、非計算性が本体)。
   - **依存 Mathlib**: §A/§B (収束)、`halting_problem` (§E、非計算性)。第 1 波 `complexity_not_computable` の
     Berry 機構を Ω に転用。
   - **難所**: 非計算性 (Ω の各 bit が停止問題を解く古典論法)。収束は壁でなく plumbing。P9 ✖ → **○〜△**。

4. **【P8 crux】K(x) ≤ -log₂ P_U(x) + c (Levin 等号方向)**
   - **何を自作**: P_U(x) の質量から長さ `≈ -log₂ P_U(x)` の prefix program を構成 (Shannon-Fano-Elias 符号)。
   - **見積行数**: **200–400 行** (第 2 波最大の山、逆向き構成)。
   - **依存 Mathlib**: Kraft (符号の存在性)、`Real.logb` / `ENNReal.log`。
   - **難所**: **これが第 2 波唯一の真の crux**。Kraft は「符号が存在する必要条件」を与えるが、
     「P_U の質量に見合う prefix program を実際に構成」する部分は Kraft の逆向きで self-build。
     P8 ✖ → **△** (Kraft 既存で下界方向 P7 は軽くなったが、等号の上界方向は依然重い)。

5. **【P10】Kolmogorov 十分統計量 / MDL (据え置き候補)**
   - **何を自作**: モデル `S ∋ x` の記述長 `K(S) + log|S|`、最小十分統計量、MDL 原理。
   - **見積行数**: **250–500 行** (定義量が多い、K の上に構築)。
   - **依存**: prefix K (自作 1)、`entropy` (§E)。
   - **難所**: 解析壁ではなく**定義量**。scouting ✖ 据え置き。第 2.5 波に隔離推奨。

**工数総括**: prefix 塔の背骨 (自作 1–4) で **490–970 行**。うち解析的に重いのは P8 crux (自作 4) のみ。
Ω 収束 (かつて壁と目された) は Kraft+summable で **plumbing 60–120 行**に縮む。

---

## Mathlib 壁の列挙 (`@residual(wall:…)` 候補)

**第 2 波に genuine な Mathlib 解析壁は無い** (Kraft が既存のため)。「不在」は全て**定義の自作 = 選択 (big)**であり
「壁 (hard analysis)」ではない。loogle confirmation:

| 不在物 | loogle query | 結果 (verbatim) | 判定 |
|---|---|---|---|
| prefix-free 述語 | `"PrefixFree"` | `Found 0 declarations whose name contains "PrefixFree".` | **非壁**: `List.IsPrefix` から数行で自作 |
| Martin-Löf randomness | `"MartinLof"` | `Found 0 declarations whose name contains "MartinLof".` | **非壁 (選択)**: P9「algorithmically random」の主張に要るが定義の選択問題。`"Martin"` は `Martingale` 127 件のみ (無関係) |
| Chaitin Ω | `"Chaitin"` | `Found 0 declarations whose name contains "Chaitin".` | **非壁 (選択)**: Ω 定義は自作、収束は Kraft 既存 |
| Kolmogorov 十分統計量 | `"Sufficient"` | `Found one declaration` (`Std.Http.Status.insufficientStorage` — 無関係) | **非壁 (選択)**: P10 定義自作 |
| Kraft-McMillan (壁と目されていた) | `"Kraft"` / `"McMillan"` | `Found one declaration` (`InformationTheory.kraft_mcmillan_inequality`) | **既存** ⟹ **壁でない** (overturn) |

> **共有 sorry-lemma の要否**: 第 1 波 plan §Out / 判断ログ #1 は `@residual(wall:prefix-free-tower)` に第 2 波を
> 一括隔離していたが、本 inventory の実測で **その "wall" の解析核 (Kraft) は既存** と判明。⟹ **`wall:prefix-free-tower`
> という単一壁 slug は誤り (over-estimation)。共有 sorry-lemma への集約は非推奨。** 第 2 波の途中 sorry は
> **object 別の `plan:` slug** に分ける (`plan:kolmogorov-prefix-machine` / `plan:kolmogorov-universal-prob` /
> `plan:kolmogorov-omega` / `plan:kolmogorov-levin` / `plan:kolmogorov-kss`)。`wall:` を打つ先は現状**無い**
> (P8 crux も「Shannon-Fano-Elias 構成という self-build」= 選択であって Mathlib 不在の解析ではない)。
> 第 1 波 plan の §Out / 判断ログ #1 は本 inventory を受けて **`wall:prefix-free-tower` の解析壁前提を撤回**する
> 更新が要る (親子整合、child = 本 inventory が newer)。

---

## 撤退ラインへの距離

親 = 第 1 波 [`kolmogorov-moonshot-plan.md`](kolmogorov-moonshot-plan.md)。その撤退ライン R1/R2 は **plain C 背骨**の
話 (frozen・未発動) で第 2 波に触れない。第 2 波が触れるのは §Out の scope-out (`wall:prefix-free-tower`) のみ。

- **触れる撤退ライン**: 第 1 波 §Out = 「prefix 塔は genuine Mathlib 壁 (未整備インフラ) として別 moonshot に隔離」。
  **判定: 隔離自体は維持 (別 moonshot が正しい)。ただし「genuine 解析壁」という前提は overturn される** — Kraft 既存に
  より、第 2 波は「壁」でなく「大きな新規定義群 (解析は Kraft で調達済)」。第 1 波 plan の §Out 文言
  (「唯一の genuine 壁」) を本 inventory で訂正する (親を child に合わせる)。
- **第 2 波の新規撤退ラインとして提案** (新 moonshot 起票時に採用):
  - **R-W2a**: prefix-free U_prefix の literal モード自己限定符号 (Elias γ / 長さ前置) が 1 セッションで組めない場合
    → **縮退**: U_prefix を「literal を持たない interpret-only 機械」に退避し、K の well-defined 性は
    「記述可能な x に限定」(P7/P9 の domain を「停止 program の像」に絞る) で先に P9 Ω (収束+非計算) を最小成果に確定。
    退避出口は `sorry + @residual(plan:kolmogorov-prefix-machine)` (hypothesis bundling 禁止、
    `IsPrefixMachineHypothesis` 等に self-delimiting 性を畳んで P8 を通したことにするのは load-bearing = 禁止)。
  - **R-W2b**: P8 等号 crux (Shannon-Fano-Elias 逆向き構成) が 400 行超で発散 → **P7 下界 + P9 Ω の 2 headline を
    第 2 波の最小成果**として先に確定 (両者は Kraft+summable で軽い)、P8 Levin は第 2.5 波へ park。
    park slug `plan:kolmogorov-levin`。

**判定 (現時点)**: 撤退ライン未発動 (第 2 波未着手)。**R-W2b が発動する公算が中程度** (P8 等号方向が唯一の重量級)。
R-W2a は literal 自己限定符号が組めれば回避可。

---

## 着手のための skeleton

`InformationTheory/Shannon/Kolmogorov/PrefixMachine.lean` (仮) の出だし。第 1 波 `UniversalMachine.lean` の
設計 (program = `List Bool`、interpret 委譲) を踏襲し、**literal を prefix-free 化**する。全 `sorry` は
type-check-done を満たす退避出口 (`@residual(plan:…)`)。

```lean
import Mathlib.Computability.PartrecCode          -- Code, eval, exists_code, Denumerable Code
import Mathlib.Computability.Encoding             -- encodeNat, decodeNat
import Mathlib.InformationTheory.Coding.KraftMcMillan  -- UniquelyDecodable, kraft_mcmillan_inequality
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal    -- ENNReal.tsum_eq_iSup_sum / sum_le_tsum / le_tsum
import Mathlib.Topology.Algebra.InfiniteSum.Real       -- summable_of_sum_le
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog -- ENNReal.log
import Mathlib.Analysis.SpecialFunctions.Log.Base       -- Real.logb
import InformationTheory.Shannon.Kolmogorov.UniversalMachine  -- 第 1 波 complexity（K ≥ C の比較）

namespace InformationTheory.Kolmogorov

open Nat.Partrec Nat.Partrec.Code
open Computability (encodeNat decodeNat)

/-- A set of bit-string programs is prefix-free (self-delimiting): no codeword is a
proper prefix of another. Building block for the prefix (self-delimiting) machine. -/
def PrefixFree (S : Set (List Bool)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a <+: b → a = b

/-- Prefix-free ⟹ uniquely decodable (standard; not in Mathlib). Feeds `kraft_mcmillan_inequality`. -/
theorem PrefixFree.uniquelyDecodable {S : Set (List Bool)} (h : PrefixFree S) :
    UniquelyDecodable S := by sorry
  -- @residual(plan:kolmogorov-prefix-machine)

/-- The fixed prefix-free (self-delimiting) universal machine. Its valid-program set is
prefix-free, so Kraft applies. `literal` mode length-prefixes the payload to stay self-delimiting. -/
noncomputable def prefixUniversalEval : List Bool → Part ℕ := by sorry
  -- @residual(plan:kolmogorov-prefix-machine)  -- self-delimiting 2-mode parse (~150–300 行)

/-- Prefix Kolmogorov complexity `K(x)`: shortest self-delimiting program producing `x`. -/
noncomputable def prefixComplexity (x : ℕ) : ℕ :=
  sInf { l | ∃ p : List Bool, p.length = l ∧ x ∈ prefixUniversalEval p }

/-- Universal probability `P_U(x) = ∑_{p : U_prefix p = x} 2^{-|p|}` in `ℝ≥0∞`
(tsum always defined; `≤ 1` from Kraft + summable). -/
noncomputable def universalProb (x : ℕ) : ℝ≥0∞ :=
  ∑' p : { p : List Bool // x ∈ prefixUniversalEval p }, (2 : ℝ≥0∞)⁻¹ ^ (p : List Bool).length

/-- Chaitin's Ω: the halting probability of the prefix machine. Well-defined (≤ 1) via Kraft. -/
noncomputable def chaitinOmega : ℝ≥0∞ :=
  ∑' p : { p : List Bool // (prefixUniversalEval p).Dom }, (2 : ℝ≥0∞)⁻¹ ^ (p : List Bool).length

/-- P7 lower bound: `P_U(x) ≥ 2^{-K(x)}` (one-term bound via `ENNReal.le_tsum`). -/
theorem universalProb_ge_two_pow_neg_prefixComplexity (x : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ prefixComplexity x ≤ universalProb x := by sorry
  -- @residual(plan:kolmogorov-universal-prob)

/-- P9: `Ω ≤ 1` (Kraft on each finite subset + summable). -/
theorem chaitinOmega_le_one : chaitinOmega ≤ 1 := by sorry
  -- @residual(plan:kolmogorov-omega)

/-- P8 Levin coding theorem (crux, equality direction is the self-build hill). -/
theorem levin_coding_theorem :
    ∃ c : ℕ, ∀ x : ℕ, x ∈ Set.range (fun p => prefixUniversalEval p) →
      |(-(Real.logb 2 (universalProb x).toReal)) - (prefixComplexity x : ℝ)| ≤ c := by sorry
  -- @residual(plan:kolmogorov-levin)

end InformationTheory.Kolmogorov
```

最初に割るのは `PrefixFree.uniquelyDecodable` (数行、Kraft への接続確認) と `prefixUniversalEval` (自作の山)。
両者が通れば P7 下界と Ω 収束は Kraft+summable+le_tsum で直線的に閉じる。P8 等号 crux が唯一の重量級。

---

## 第 1 波 inventory との差分 (settled facts 候補)

以下は machine/loogle 確認済み。第 2 波 moonshot 起票時に `docs/kolmogorov/kolmogorov-facts.md` へ確定推奨:

- **claim (overturn、confidence = `loogle-neg` + machine)**: 「prefix 塔 = 唯一の genuine 解析壁」(scouting §0) は
  **Kraft の解析核については誤り**。`InformationTheory.kraft_mcmillan_inequality`
  (`Mathlib/InformationTheory/Coding/KraftMcMillan.lean:149`、有限 UD 符号版) + `summable_of_sum_le`
  (`InfiniteSum/Real.lean:84`) + `ENNReal.tsum_eq_iSup_sum` が Ω/P_U 収束を供給。
- **再検証コマンド**: loogle `"Kraft"` → Found 1、`"PrefixFree"`/`"MartinLof"`/`"Chaitin"` → Found 0。
  `Read Coding/KraftMcMillan.lean:149` + `Coding/UniquelyDecodable.lean:35`。
- **含意**: 第 2 波は「壁」でなく「新規定義群 (解析は調達済)」。`@residual(wall:prefix-free-tower)` 単一壁 slug は
  撤回し、object 別 `plan:` slug に分割。genuine `wall:` を打つ先は現状 **無い**。
</content>
</invoke>

# Ch.14 Kolmogorov 複雑性 (plain C 背骨) ムーンショット計画 🌙

**Status**: 第 1 波達成 (2026-07-24) — **flagship `kolmogorov_entropy_rate` 完全 proof-done・sorryAx-free・
無条件** (`EntropyRate.lean:1036`)。gateway atom (Phase U + P1 + P2) は 2026-07-20 に PASS、P3/P5 も proof-done、
**P4 flagship の上界も R1–R4 再アーキで closure** ⟹ 第 1 波背骨 (P1–P5) が全 proof-done。roadmap scope-out は
解除相当。残る P6 SLLN は stretch (第 1 波成否に無影響)。prefix 塔 (P7–P9) は第 2 波 = 別 moonshot に隔離し、
本計画の scope 外。

> **SoT**: 山場マップ + 定義形は [`kolmogorov-scouting.md`](kolmogorov-scouting.md) §4 (**訂正済み定義形**)、
> per-lemma 台帳は [`kolmogorov-mathlib-inventory.md`](kolmogorov-mathlib-inventory.md)。本計画は両者を
> 実装 Phase に落とす制御文書。壁断定・settled fact はここに散文で書かず slug / 再検証コマンドで参照する。

## 進捗 (DAG)

- [x] Phase M0 — Mathlib API 在庫調査 ✅ → [`kolmogorov-mathlib-inventory.md`](kolmogorov-mathlib-inventory.md)
- [x] Phase U — 長さ加法専用万能機械 U の構成 ✅ proof-done sorryAx-free (`UniversalMachine.lean` 108 行、gateway PASS)
- [x] Phase P1 — 不変性定理 ✅ proof-done + `@audit:ok` (`invariance` / `invariance_code`、pointwise 形)
- [x] Phase P2 — 上界 (literal モード) ✅ proof-done + `@audit:ok` (`complexity_le_natLen`)
- [x] Phase P3 — 数え上げ + 非圧縮存在 ✅ proof-done sorryAx-free (`Counting.lean` 131 行、`incompressible_count`/`exists_incompressible`/`complexity_lt_finite`、自作 `progNat` 自己限定符号で `{x|C(x)<k}` を `Ico 1 (2^k)` へ単射、commit `ea11edf7`)
- [x] Phase P4 — K↔H エントロピー率 (**flagship** `@[entry_point]`) ✅ **完全 proof-done sorryAx-free @audit:ok**。
  `EntropyRate.lean:1036`: `kolmogorov_entropy_rate` を上界/下界 2 半分 + squeeze で outright 証明 (`#print axioms` =
  `[propext, Classical.choice, Quot.sound]`、load-bearing hyp なし)。**下界** = 6 helper (`blockLaw_eq_pi` +
  `typicalSet_blockProb_le` + `condIncompressible_count` + Markov + `floor_mul_div_tendsto`) で proof-done。**上界** =
  method-of-types 7 helper (下 §Phase P4 上界分解)、旧 crux #4 のレート欠陥判明後に再アーキ R1–R4 で closure
  (base-card `encodeBlock` `94b8b1f6` / div-mod decoder `7a529ce8` / natLen utility `167a62f4` / #6→#5→flagship
  `70f02e93`+`2e0d7138`、全 proof-done sorryAx-free、両ゲート PASS)。詳細 = 子 plan (§Sub-plan 一覧)。
- [x] Phase P5 — 非計算可能性 ✅ proof-done + `@audit:ok` (`Noncomputable.lean`、実 headline = 条件版
  `condComplexity_not_computable (y)` `¬ Computable (C(·|y))` [任意固定 y = strictly stronger] `@[entry_point]` +
  無条件系 `complexity_not_computable` [y=0]、Berry 論法、両ゲート PASS、commits `755f0024`/`39d07c2f`)
- [ ] Phase P6 — 非圧縮列の SLLN (stretch) 📋

**第 1 波 完了 (cold-read 用)**: P1–P5 が全 proof-done ⟹ 第 1 波背骨に未完 leg は無い。flagship
`kolmogorov_entropy_rate` は上界 (method-of-types 再アーキ R1–R4) / 下界 (数え上げ + AEP) の両半分 + squeeze で
完全 proof-done sorryAx-free @audit:ok。残る P6 SLLN は stretch (第 1 波成否に無関係)。第 1 波背骨に壁 residual は無い
(唯一の genuine 壁は第 2 波 prefix 塔、slug は §Out が保持)。

**次 leg 戦略 (control state)**: 第 1 波は達成済み。残る作業は (a) P6 SLLN (stretch、余力次第) と
(b) flag-only cosmetic (flagship の未使用 `[DecidableEq α]` 除去 / 内部補助補題の docstring 除去 / `witness`
naming、子 plan §follow-up、いずれも proof-done 非阻害)。第 2 波 prefix 塔 (P7–P9) は別 moonshot。

## Sub-plan 一覧

| 子 plan | scope | 状態 | backlink |
|---|---|---|---|
| [`kolmogorov-p4-upper-decoder-plan.md`](kolmogorov-p4-upper-decoder-plan.md) | P4 上界 decoder 再アーキ (R1 base-card `encodeBlock` / R2 div-mod decoder + `Partrec₂` / R3 natLen utility / R4 #5/#6 closure、method-of-types crux) | ✅ COMPLETE (R1–R4 landed、flagship 完全 proof-done) | 親 §Phase P4 上界分解 |

## ゴール / Scope

**最終到達点 (flagship)**: i.i.d. 情報源に対する Kolmogorov 複雑性のエントロピー率
`(1/n) E[C(X^n | n)] → H(X)` (CT 2nd ed Thm 14.3.1、番号は着手前に PDF 照合)。これを `@[entry_point]`
headline `kolmogorov_entropy_rate` として掲げ、計算量↔情報量の合流を本章の意味とする。

**In (第 1 波、plain 複雑性 C)**: P1 不変性 → P2 上界 → P3 数え上げ/非圧縮 → **P4 K↔H (flagship)** →
P5 非計算可能性。余力で P6 SLLN。headline 4–5 本、すべて既存 Mathlib 万能機械 (`Nat.Partrec.Code`) +
project の entropy/AEP 資産で閉じる見込み。

**Out (第 2 波 = 別 moonshot、本計画に持ち込まない)**: prefix-free 機械インフラ自作 → P7 普遍確率 →
P8 符号化定理 (Levin) → P9 Chaitin の Ω。ここが唯一の genuine Mathlib 壁 (未整備インフラ) であり、
`@residual(wall:prefix-free-tower)` に隔離。P10 Kolmogorov 十分統計量も先送り。

**非ゴール**: Mathlib への PR / upstream、bit↔nat 精密変換の作り込み、prefix 複雑性 K への一般化。

---

## Approach

### 背骨全体の DAG

```
        Phase U  長さ加法専用万能機械 U の構成 (foundation, crux)
                 │  U が組めれば C(x|y) が well-defined (literal echo で非空 ⟹ Nat.sInf 到達)
                 ▼
        Phase P1 不変性定理 (gateway atom)  C_U(x) ≤ C_A(x) + c_A
          │  exists_code で別機械 A を eval c_A に落とし、固定 selector を前置
          ▼
   ┌──── Phase P2 上界 ────┐  literal モード ⟹ C(x) ≤ l(x) + O(1)、条件版 C(x|l(x)) ≤ l(x)+c
   │                       │
   ▼                       ▼
Phase P3 数え上げ        (P2 条件上界)
 非圧縮存在                 │
   │                       ▼
   │            ┌── Phase P4 K↔H (flagship @[entry_point]) ──┐
   │            │   上界 = P2 条件上界 + typical set 符号化       │
   │            │   下界 = P3 数え上げ + AEP                     │
   ▼            ▼                                              │
Phase P6 SLLN   Phase P5 非計算可能性 ✅ (Berry、P1/P3 のみ依存)  │
 (stretch)      (proof-done、並走レーン的中)   P4 完全 proof-done ✅ ┘
```

### なぜ naive 定義が壊れ、専用 U が要るか (crux の核心)

当初案 `C(x) := sInf { Nat.size p | x ∈ eval (ofNat Code p) 0 }` (プログラム = Gödel 数 `p`、
長さ = `Nat.size (encodeCode c)`) は **P2 上界すら成立せず P4 flagship を破壊する** ため棄却済み。
機械確認済みの settled fact であり、本計画本体では再導出せず inventory の walls 節を参照する
(再検証は `docs/kolmogorov/kolmogorov-facts.md` 候補、下記「settled facts 参照」節)。要点のみ:
`Code.const` が unary 反復合成ゆえ `encodeCode (const n)` が二重指数に膨張し、`x` を出力する最短
プログラムのコストが `≈ 2^x` bit に化けて `C(x) ≤ l(x)+c` が偽になる。AST ノード数を長さに採る逃げ道も
`const x` の unary 塔で封じられ、**Gödel 数でも AST でも加法定数は原理的に出ない**。これは Mathlib 壁
ではなく「間違った長さ尺度を選んだ」定義形の選択問題 (loogle 0-hit ではない)。

### 長さ加法モデル (採る形)、U の 2 モードが P1/P2 をどう担保するか

- **プログラム = bit 列** (`ℕ` を `encodeNat` で bit 列視、または `List Bool`)、長さ `l(p) := (encodeNat p).length`。
- **専用 U を自作** (Phase U、make-or-break):
  - **literal モード** `U (0 ∷ x_bits) = x` ⟹ echo プログラムが `l(x) + O(1)` を実現 ⟹ **P2 上界を担保**。
  - **interpret モード** `U (1 ∷ selfDelim(idx) ∷ input) = eval (ofNat Code idx) input` ⟹ 固定
    selector `1 ∷ selfDelim(c_A の idx)` の前置が加法定数 `c_A` を生む ⟹ **P1 不変性を担保**。
    `selfDelim` は idx を可逆に埋める自己限定符号化 (prefix-free 塔とは無関係、単なる idx の埋め込み)。
- **両モード非空性が well-defined 性を担保**: literal モードが常に非空を供給 ⟹ `Nat.sInf` が最小値に到達
  (`Nat.sInf_mem`) ⟹ 定義本体に `sorry` を置かずに済む。

一言でいえば、**U の構成が本章の crux**。literal モードが P2 を、interpret モードが P1 不変性を、
両モード非空性が well-defined 性を、それぞれ担保する。`(encodeNat ·).length` を長さに採ることで数え上げ
P3 は `Nat` / `List` 初等補題で閉じる。

### 実装原則

- **Skeleton-driven**: 各 Phase は全補題を `:= by sorry` で建て、type-check done を確認してから 1 sorry ずつ充填。
- **並走レーン**: P3 / P5 は U の詳細 (実行の存在性・非計算性のみ) に依存しないため、Phase U が長引く間も
  独立に先行取得できる (撤退ライン R2 の最小成果でもある)。
- **既存資産は read-only 消費**: P4 は project の AEP 資産 (`typicalSet_card_le` 等) を**署名変更せず**
  消費する。既存 shared lemma の signature 変更は本計画に無いため consumer ripple 解析 (dep_consumers) は不要。

---

## 定義形 (Mathlib-shape-driven、scouting §4 訂正形 = SoT、条件版 primary)

```lean
import Mathlib.Computability.PartrecCode   -- Code, eval, exists_code, smn, curry, encodeCode
import Mathlib.Computability.Halting        -- halting_problem, rice
import Mathlib.Computability.Encoding        -- encodeNat : ℕ → List Bool (長さ加法モデルの長さ)
import Mathlib.Data.Nat.Size                 -- Nat.size_le (P3 数え上げ)
import Mathlib.Order.Lattice.Nat             -- Nat.sInf_mem / sInf_le (well-defined 性)

namespace InformationTheory.Kolmogorov

/-- 固定万能機械: bit 列プログラム `p`（`literal` / `interpret` の 2 モードを parse）を条件 `y` の下で走らせる。
    長さ加法を担保する専用構成。**核心の自作物**（skeleton では body を sorry へ退避）。 -/
noncomputable def universalEval (p y : ℕ) : Part ℕ := /- U の code 構成に依存、Phase U で確定 -/ sorry

/-- プログラム長（長さ加法モデル）: `(encodeNat p).length`。naive 版は `Nat.size p`（P3/P5 のみで併用可）。 -/
def progLen (p : ℕ) : ℕ := (Encodable.encodeNat p).length   -- 実際の名前は Phase U で確定

/-- 条件付き Kolmogorov 複雑性 `C(x | y)` を primary に。`universalEval` の実行結果が `x` になる最短
    プログラム長。非空性は literal モード echo から ⟹ `Nat.sInf` が到達最小値（定義本体に sorry 不要）。 -/
noncomputable def condComplexity (x y : ℕ) : ℕ :=
  sInf { l | ∃ p, progLen p = l ∧ x ∈ universalEval p y }

/-- 無条件複雑性 `C(x) := C(x | 0)`。 -/
noncomputable def complexity (x : ℕ) : ℕ := condComplexity x 0
```

**設計上の注意** (inventory Key-preconditions box):
- `x ∈ universalEval p y` の `∈` は `Part.Mem` (実行結果)。`f ∈ c` の Code-membership とは別物 (混同注意)。
- 条件 `y` は入力に直接与える規約 (`eval c y`) で統一。curry / `Nat.pair` は「無条件化 (y を code に畳む)」に
  のみ使い、P4 の `C(X^n | n)` で `y = n` が第一座標に来る規約を崩さない。
- `Nat.sInf_le` は `protected` — フル修飾で呼ぶ。

---

## Phase 詳細

各 Phase: 依存 / 成果物 (signature 略式) / 見積行数 / proof-log / 撤退ライン。

### Phase M0 — Mathlib API 在庫調査 ✅

- **状態**: DONE。[`kolmogorov-mathlib-inventory.md`](kolmogorov-mathlib-inventory.md) (318 行) が SoT。
  意味論層 (`Code`/`eval`/`evaln`/`exists_code`/`smn`/停止問題/符号化) は Mathlib に 100% 完備、
  P4 接続資産 (entropy/typicalSet/…) も project に既存と確認済み。
- **proof-log**: no (調査 Phase)。

### Phase U — 長さ加法専用万能機械 U の構成 (foundation, crux) 📋

- **依存**: なし (背骨の礎)。**make-or-break** — ここが通れば残り (P1–P5) は直線的、詰まれば定義形を再設計。
- **成果物**: `universalEval : ℕ → ℕ → Part ℕ` の具体構成 (`Nat.Partrec.Code` として組み `eval` を verbatim 確定)、
  `progLen`、`condComplexity` / `complexity` の定義、well-defined 性補題 (literal echo で非空 ⟹ `sInf_mem`)。
  2 モード parse (literal `0 ∷ x` / interpret `1 ∷ selfDelim(idx) ∷ input`) の実行証明。
- **見積行数**: 100–300 行 (Mathlib に既製の「入力を parse する万能 code」は無く、`prec`/`rfind'` の手組みが重い)。
  ファイル `UniversalMachine.lean`。
- **proof-log**: **yes** (gateway atom を含む foundation、metrics をデモ資産として取得)。
- **撤退ライン**: 構成が 300 行を超えて発散 → **R2 発動** (P1/P2/P4 を丸ごと park、P3+P5 を最小成果に、下記)。

### Phase P1 — 不変性定理 (gateway atom の核) 📋

- **依存**: Phase U。
- **成果物 (実装済、pointwise 形)**: `invariance (A) (hA : Partrec₂ A) : ∃ b, ∀ x y q,
  x ∈ A (decodeNat q) y → condComplexity x y ≤ q.length + b`。**pointwise-over-descriptions 形**を採用
  (旧 min-RHS 形 `∀ x, complexity x ≤ C_A x + c` は Lean 上で偽 — `sInf ∅ = 0` ゆえ A で記述不能な x に対し
  `C_A x = 0` となり全 x で `complexity x ≤ c` を主張してしまう)。pointwise 形は min-RHS 形を含意する
  **strictly stronger** な honest 核 (記述集合非空なら最小 q で instantiate)。honesty 監査 PASS。
  機構: A を `exists_code` で `eval c_A` に落とし、interpret selector を前置、加法定数 `b = encodeCode c + 2`。
- **見積行数**: 加法翻訳補題は U が組めれば 20–40 行。P1 全体で 40–80 行。ファイル `Invariance.lean`。
- **proof-log**: **yes** (gateway atom の一部)。
- **撤退ライン**: 1 セッション内に加法定数 `l(q)+c_A` を出せない → **R1 発動** (optimality 形退避、下記)。
  退避出口は `sorry + @residual(plan:kolmogorov-invariance-additive)`。`IsUniversalHypothesis` 等に
  不変性を畳んで P4 を「通ったことにする」load-bearing bundling は禁止。

### Phase P2 — 上界 (literal モード) 📋

- **依存**: Phase U (literal モード)。
- **成果物**: `upper_bound : ∃ c, ∀ x, complexity x ≤ progLen x + c` (無条件)、条件版
  `cond_upper_bound : ∃ c, ∀ x, condComplexity x (progLen x) ≤ progLen x + c`。literal echo プログラム
  `0 ∷ x_bits` の実行 (`universalEval` literal 分岐) + `sInf_le` で初等。
- **見積行数**: 30–60 行 (U の literal 分岐が確定していれば軽い)。`Invariance.lean` に同居可 (1500 行未満)。
- **proof-log**: no。
- **撤退ライン**: literal モードが U と共倒れ → R2 (P2 も P1/P4 と共に park)。単独退避は `sorry +
  @residual(plan:kolmogorov-p2-upper)`。

### Phase P3 — 数え上げ + 非圧縮存在 (低リスク・並走可) 📋

- **依存**: `complexity` の存在のみ (U の実行詳細に非依存 ⟹ **並走レーン**)。naive `Nat.size` 定義でも閉じる。
- **成果物**: `incompressible_count (k : ℕ) : #{x | complexity x < k} < 2^k` (有限性 +
  `x ↦ 最小プログラム` の `card_le_card_of_injOn` + `Nat.size_le` + `card_range` + `Nat.lt_two_pow_self`)。
  系: 非圧縮列の存在 `∃ x, k ≤ complexity x`。
- **見積行数**: 30–50 行 (iconic・小、既存資産だけで閉じる唯一の主要 leg)。ファイル `Counting.lean`。
- **proof-log**: no。
- **撤退ライン**: 発動見込み低。R2 の最小成果の 1 本 (park しても単独完成させる)。

### Phase P4 — K↔H エントロピー率 (flagship `@[entry_point]`) ✅

- **状態**: 完全 proof-done sorryAx-free @audit:ok (`EntropyRate.lean:1036`)。上界/下界 2 半分 + squeeze で
  outright 証明。下段は着地署名 (`@[entry_point]` 形) + 証明戦略の参照。
- **依存**: P2 条件上界 (加法定数) + P3 数え上げ + project AEP 資産。
- **成果物** (`@[entry_point]`):
  ```lean
  theorem kolmogorov_entropy_rate
      {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : ℕ → Ω → α) (hiid : /- i.i.d.: iIndepFun + IdentDistrib -/)
      (hpos : ∀ a, 0 < (μ.map (Xs 0)).real {a}) :
      Tendsto (fun n => (1/n) * ∫ ω, (condComplexity (encodeBlock n (jointRV Xs n ω)) n : ℝ) ∂μ)
              atTop (𝓝 (entropy μ (Xs 0) / Real.log 2))
  ```
  RHS は `/ Real.log 2`: `entropy` は自然対数 nat 基底、`condComplexity` は 2 進 bit 基底ゆえ
  bit-rate を nat-entropy に合わせる変換が要る。着地署名 (full i.i.d. hyps 継承) は `EntropyRate.lean` が SoT。
- **証明戦略** (inventory 主定理節): 上界 = typical set 内 index 符号化 (`program = ⟨復号器⟩ ++ ⟨index⟩`、
  長さ `c_dec + n(H+ε)`) を P2 条件上界に載せ、`typicalSet_card_le` で `|A_ε^n| ≤ exp(n(H+ε))`、非 typical
  は `typicalSet_prob_tendsto_one` で吸収 ⟹ `E[C]/n ≤ H+ε+o(1)`。下界 = P3 数え上げ
  `#{C(x^n|n) < n(H-ε)} < 2^{n(H-ε)}` + `stronglyTypicalSet_card_ge_eventually` (~exp(nH) 個に分散) ⟹
  `E[C]/n ≥ H-ε-o(1)`。squeeze。
- **ファイル**: `EntropyRate.lean` (上界の decoder crux は `EntropyRateUpper.lean` に外部化)。
- **撤退ライン**: 未発動 (closure 済)。`kolmogorov-p4-upper` / `kolmogorov-p4-lower` / `kolmogorov-p4` slug は
  いずれも live residual 無し (flagship 本体は 2 半分 + squeeze で outright 証明、residual なし)。

### Phase P4 上界分解 (method of types、7 helper) ✅

**上界 `kolmogorov_entropy_rate_upper` は 7 helper 全 proof-done で closure 済み。** 上界 = method of types。
program = `⟨型記述子 c⟩ ++ ⟨index i⟩` を `invariance` に食わせ、長さ `≈ |α|·log n + n·(H+ε)` を得て組む。7 helper:

| # | lemma 名案 | 提供先 / 主依存資産 `file:line` | 難度 / 状態 |
|---|---|---|---|
| 1 | `typeClassByCount_card_le` (**raw 形** `(\|T_c\|:ℝ) ≤ n^n / ∏ a (c a)^{c a}`) | `Sanov/MultinomialLowerBound.lean` (public) | ✅ proof-done `475293d1` |
| 2 | `numTypes_le` (`(piAntidiag univ n).card ≤ (n+1)^\|α\|`、旧 private `piAntidiag_card_le` を de-privatize+rename) | `Sanov/MultinomialLowerBound.lean` (public) | ✅ proof-done `475293d1` |
| 3 | `entropyByCount_le_of_strongTypical` (強典型上で `entropyByCount ≤ H + ε·logSumAbs`) | `EntropyRate.lean:114` 付近 (既存 `conditionalKL_HXemp_le` の wrapper) | ✅ proof-done `979a10a4`+`76a18d6d` |
| **4** | `typeDecoder_partrec` (`Partrec₂`) ★crux | `EntropyRateUpper.lean` (div-mod pack + base-card 出力) | ✅ proof-done sorryAx-free `7a529ce8` (旧設計レート無効 → R2 で div-mod packing に再設計) |
| 5 | `condComplexity_block_typical_le` (典型 per-string 上界) | `EntropyRate.lean` | ✅ proof-done `2e0d7138` (R4b/R4c: matching 補題 + entropyByCount 会計) |
| 6 | `condComplexity_block_uniform_le` (uniform O(n) 上界) | `EntropyRate.lean` | ✅ proof-done `70f02e93` (R4a: literal echo + `encodeBlock_lt` + `natLen_le_of_lt_two_pow`) |
| 7 | 積分組立 (`kolmogorov_entropy_rate_upper` body) | `EntropyRate.lean`、#5/#6 を消費 | ✅ proof-done `334b2e4e` (encoding 非依存、unconditional body) |

**closure の要 (完了、詳細 = 子 plan [`kolmogorov-p4-upper-decoder`](kolmogorov-p4-upper-decoder-plan.md))**:
decoder は `invariance_code` の加法定数 `b = encodeCode c + 2` が c のみ依存ゆえ **n を入力に取る単一
`Partrec₂` code** で建てた (per-n 別 code は b 発散で o(n) 崩壊)。旧 crux #4 のレート欠陥 (`Nat.pair` packing の
index 2 倍化 + `encodeBlock` doubly-exp 長さ) を base-card encoding + div/mod packing に再アーキ (R1–R2) して解消。
#5 は `typeDecoder` を `invariance` に食わせ matching 補題 `encodeBlock n b ∈ typeDecoder m n` + #1 raw→exp bridge
で消費、#6 は literal echo で closure。

**#5 が消費する #1–#3 の設計形 (expensive-to-re-derive、cache 可)**:
- #1 は **raw 形** `(\|T_c\|:ℝ) ≤ n^n / ∏ a (c a)^{c a}` で提供 (exp 形でない)。理由 = `entropyByCount` を持つ
  `TypeClassLowerBound.lean` が `MultinomialLowerBound` を transitively import する **import cycle** ゆえ exp 形は
  同居不可 (下界側 `_ge` sibling と同規約)。#5 は public bridge `pow_div_prod_pow_eq_exp_n_entropyByCount`
  (`TypeClassLowerBound.lean:55`、`n^n/∏c^c = exp(n·entropyByCount c n)`) で raw→exp 変換して #3 と接続する。
- #3 は既存 `conditionalKL_HXemp_le` (`ConditionalMethodOfTypes/Mass/Concentration.lean:786`、public) の直接
  wrapper。`EntropyRate.lean` は Concentration を import 済 (cycle なし)。

### Phase P5 — 非計算可能性 (並走レーン) ✅

- **依存**: P1 / P3 のみ (P4 と独立に走れた = relay 並走レーン、的中)。
- **成果物 (実装済)**: 実 headline は**条件版** `condComplexity_not_computable (y : ℕ) : ¬ Computable
  (fun x ↦ condComplexity x y)` (任意の固定条件 `y` で `C(·|y)` 非計算) = min-RHS 形より **strictly stronger**、
  `@[entry_point]` + `@audit:ok`。無条件版 `complexity_not_computable : ¬ Computable complexity` はその `y=0`
  系 (1 行特殊化)。手法 = Berry 論法 (`Nat.rfind` 探索機械が `invariance` を read-only 消費、`exists_incompressible`
  / `condComplexity_lt_finite` 由来の非有界性で rfind 停止性、`natLen` 対数上界の自作 growth 補題)。
  ファイル `Noncomputable.lean` (登録済)。
- **proof-log**: no。
- **撤退ライン**: 未発動 (closure 済)。`kolmogorov-noncomputable` slug は不使用のまま。commits `755f0024`/`39d07c2f`。

### Phase P6 — 非圧縮列の SLLN (stretch) 📋

- **依存**: P3 数え上げ + 既存確率補題。余力があれば。
- **成果物**: 非圧縮列 `C(x_1..x_n|n) ≥ n` なら 1 の頻度 → 1/2 (CT Thm 14.5.1)。
- **見積行数**: 中量 (80–150 行想定)。ファイル `Incompressible.lean`。
- **proof-log**: no。
- **撤退ライン**: stretch につき未達なら park のみ (`sorry + @residual(plan:kolmogorov-slln)`)、第 1 波の
  成否には影響しない。

---

## gateway atom (make-or-break) ✅ PASSED (2026-07-20)

**3 点セット = Phase U 構成 + P1 不変性 + P2 literal 上界** を 1 本で proof-done sorryAx-free + honesty 監査
all-OK。背骨の残り (P3–P5) は既存資産で直線的に閉じ、flagship P4 も closure ⟹ roadmap scope-out 解除相当。
確定した設計学習は判断ログ #2 に集約。

---

## 撤退ライン (frozen slug、未発動)

第 1 波 closure 達成につき R1 (P1 optimality 退避、frozen slug `kolmogorov-invariance-additive`) / R2 (P3+P5
最小成果先取り、frozen slug `kolmogorov-universal-machine`) はいずれも **未発動**。frozen slug は他文書参照
ありうるため register に history として残す (live residual 無し)。

---

## P4 接続資産 (inventory §6、read-only 消費)

すべて project に既存。P4 は署名変更せず消費する (consumer ripple 解析不要):

| 資産 | file:line | P4 での役割 |
|---|---|---|
| `entropy μ Xs` | `InformationTheory/Shannon/Bridge.lean:40` | 右辺 `H(X)` |
| `typicalSet μ Xs n ε` | `InformationTheory/Shannon/AEP/Basic/Core.lean:214` | 上界の符号化対象 |
| `typicalSet_card_le` | `AEP/Basic/Core.lean:247` | 上界 index bits `≈ n(H+ε)` を供給 |
| `typicalSet_prob_tendsto_one` | `AEP/Basic/Core.lean:365` | 非 typical の確率吸収 |
| `stronglyTypicalSet` | `InformationTheory/Shannon/StrongTypicality.lean:58` | 下界 (AEP 側) |
| `stronglyTypicalSet_card_ge_eventually` | `StrongTypicality.lean:446` | 下界「~exp(nH) 個に分散」 |

**plumbing 注意**: project 側は `Real.exp (n·(H±ε))` 形なので、複雑性側の `progLen` (2 進長) を
`Real.log`/`2^·` 基底に揃える橋 (`Real.log 2` の掛け合わせ) が P4 本体に要る。**前提の継承**:
`typicalSet_card_le` の full-support `hpos` と `stronglyTypicalSet_card_ge_eventually` の独立性 3 点
(`iIndepFun` + `Pairwise ⟂` + `∀ i, IdentDistrib`) を P4 の signature が漏れなく継承すること
(inventory Key-preconditions box)。

---

## settled facts 参照

CLAUDE.md「Don't cache settled facts」に従い、壁断定・二重指数の導出は本計画本体に散文で持たない。
以下を **facts 台帳候補** として、gateway atom leg で `docs/kolmogorov/kolmogorov-facts.md` に確定させる
(machine 確認済み、confidence = `machine`):

- **claim**: naive `Nat.size ∘ encodeCode` は非加法 — `encodeCode (Code.const n)` が二重指数に膨張し
  `C(x) ≤ l(x)+c` が偽。
- **再検証コマンド**: `PartrecCode.lean:96` (`Code.const` の unary 反復) + `:14` (`encodeCode (comp _ _)` の
  `Nat.pair` 二次) を Read。loogle `Nat.Partrec.Code.eval (Nat.Partrec.Code.comp _ _)` → Found 0、
  `Nat.size (Nat.pair _ _)` → Found 0 (いずれも「加法翻訳補題は Mathlib 不在」ではなく「非加法な定義形」を示す)。
- **含意**: これは Mathlib 壁ではない。plain C 背骨に genuine Mathlib 壁は無く、`@residual(wall:…)` を打つ先は
  第 2 波の prefix 塔 (`wall:prefix-free-tower`) のみ。第 1 波の途中 sorry は全て `@residual(plan:…)`。

- **claim (上界 decoder、proof-pivot-advisor 診断 2026-07-20、confidence = `loogle-neg`)**: method-of-types
  family (`Sanov/MultinomialLowerBound.lean`・`TypeClassLowerBound.lean`・`StrongTypicality.lean`) に
  `Partrec`/`Computable` 参照は **0 件**、Mathlib に `Computable` × `List.filter` の橋は **loogle Found 0**。
- **含意**: 上界 crux #4 decoder (`typeDecoderPartrec`) は既存資産で軽くならない genuine real work。**しかし
  全有限・decidable ゆえ原理 computable = 「選択 (big)」であって「壁 (hard)」ではない** — `@residual(wall:…)` は
  打たず `@residual(plan:kolmogorov-p4-upper-decoder)`。詳細 = 子 plan
  [`kolmogorov-p4-upper-decoder-plan.md`](kolmogorov-p4-upper-decoder-plan.md) §settled facts。

---

## ファイル構成 / 分割方針

新 family dir `InformationTheory/Shannon/Kolmogorov/` 配下 (scouting skeleton の
`InformationTheory/Kolmogorov/` から本計画で `Shannon/` 配下に確定 — 判断ログ参照)。各ファイル 1500 行未満:

- `UniversalMachine.lean` — Phase U (U 構成 + `condComplexity`/`complexity` 定義 + well-defined 性)
- `Invariance.lean` — Phase P1 + P2 (加法翻訳 + 上界)
- `Counting.lean` — Phase P3 (数え上げ/非圧縮、並走レーン)
- `EntropyRate.lean` — Phase P4 flagship (超過見込み時は `…Upper.lean` / `…Lower.lean` に分割)
- `Noncomputable.lean` — Phase P5 (並走レーン)
- `Incompressible.lean` — Phase P6 (stretch)

各ファイル追加時に `InformationTheory.lean` へ import 行を登録。`private` helper を共有する sub-module は
同一ファイルに置く (file-scoped `private`)。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正時。決着済 entry は削除 (git が履歴)、active な判断のみ残す。

1. **prefix 塔の隔離 (active)**: P7–P9 は第 2 波 = 別 moonshot、本計画に prefix 依存を持ち込まない。genuine
   Mathlib 壁 (`wall:prefix-free-tower`) はそこに集約し、第 1 波背骨には壁 residual を作らない。
2. **継承される設計不変条件 (settled、§定義形 + P1 成果物 が継承)**: gateway atom PASS (2026-07-20) で確定した 3 点:
   (i) **interpret モードは Mathlib `eval` に委譲** (U を `prec`/`rfind'` で再構成しない) — これが「専用 U 手組み 300 行」
   リスクを消し U=108 行に。万能性は `exists_code` が独立に確立、invariance はそれを消費するのみ (循環なし)。
   (ii) **program = `List Bool`** (ℕ-as-binary でなく) — `List.length`/`append` で長さ加法が edge case なしに成立
   (`Nat.size` は p=0 で先頭ゼロ消失により cons 加法性が壊れる)。§定義形の `p : ℕ` 表記は `List Bool` に読み替え、
   複雑性関数の型 `ℕ → ℕ → ℕ` は維持、program だけ bit 列。
   (iii) **P1 は pointwise 形** (Phase P1 成果物、min-RHS 形は sInf ∅ 退化で偽)。

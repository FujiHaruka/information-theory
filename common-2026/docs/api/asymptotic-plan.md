# I-3 Asymptotic / Exponent Framework サブ計画

> **Parent**: [`../textbook-roadmap.md`](../textbook-roadmap.md) §「Tier ∞ — Infrastructure / I-3. Asymptotic / exponent framework」
> 実態整合 (2026-05-20): DONE-UNCOND — Phase 1〜4 完了済 (進捗欄 📋 は STALE)。`InformationTheory/InformationTheory/Asymptotic.lean` に `DotEq` (`:43`、`IsLittleO` 実定義、`True` ではない) + `refl`/`symm`/`trans`/`mul`/`inv` + `dotEq_iff_tendsto_log_div` (`:116`) + `exp_decay_N_of_pos` (`:148`、constructive witness で実証) が存在。`lake env lean` silent、0 sorry。`dotEq_iff_tendsto_log_div` は `InformationTheory/Shannon/ChernoffInformation.lean` で実利用。
> **Status (2026-05-18)**: 起草。在庫調査 ([`asymptotic-mathlib-inventory.md`](asymptotic-mathlib-inventory.md)) 完了直後。
> **規模**: 1 ファイル 80〜150 行、1〜2 セッション (合計 1.5〜3 時間)。新数学なし、新規 `def` 1 個 (`DotEq`) + 基本性質 lemma 4〜6 個 (`refl`/`symm`/`trans`/`mul`/`inv`) + closed-form rate extraction wrapper 1〜2 個 + `o(n)` notation 説明 docstring。

## 進捗

- [x] M0 在庫調査 ✅ → [`asymptotic-mathlib-inventory.md`](asymptotic-mathlib-inventory.md)
- [x] Phase 1 — skeleton ✅ 実態整合 2026-05-20
- [x] Phase 2 — alias / 基本性質充填 (`refl`/`symm`/`trans`/`mul`/`inv`) ✅ 実態整合 2026-05-20
- [x] Phase 3 — `exp_decay_N_of_pos` + `dotEq_iff_tendsto_log_div` bridge + `example` ✅ 実態整合 2026-05-20
- [x] Phase 4 — verify (`lake env lean` silent) ✅ 実態整合 2026-05-20

## A. Context

### モチベーション

教科書 (Cover-Thomas) の `\doteq` (exponent equality, `a_n ≐ b_n ⟺ (1/n) log (a_n/b_n) → 0`) と `o(n)` 漸近表記を Lean に持ち込み、後続 seed (T1-B Chernoff, T1-C Cramér, T2-A AWGN converse, T3-B MAC converse, T4-A LZ78 等) で大量に登場する `Tendsto (fun n => (1/n) * Real.log (...)) atTop (𝓝 (-C))` パターン (在庫 §B の 8 ファイル横断 inline 表現) を **統一する notation + 述語層** を作る。

本タスクは Cover-Thomas 形式化の 3 層成果物 (verified library / typed RV API / 教科書原稿) の **真ん中の層 (typed RV API)** のうち、漸近系・rate 系を担う。I-1 typed RV API (`H(X)`, `I(X;Y)`, `D(X‖Y)`) と並行する独立層。**I-1 の typed RV API は本 I-3 では参照しない** (I-3 は measure-theoretic レベルの一般 wrapper、`a, b : ℕ → ℝ` の sequence rate を扱うのみ)。

### 在庫調査の結論 (verbatim 再掲しない、in-essence 5 点)

1. Mathlib `Asymptotics.IsBigO` / `IsLittleO` / `IsTheta` / `IsEquivalent` の **4 種述語 + notation** (`=O[l]`, `=o[l]`, `=Θ[l]`, `~[l]`) は **完備**。教科書 `O(n)` / `o(n)` / `Θ(n)` / `~` は **既存 1 行**で書ける (在庫 §A-1, §A-7)
2. Mathlib `Analysis/Asymptotics/ExpGrowth.lean` (2025 新規) が `expGrowthInf` / `expGrowthSup` (`= liminf/limsup ((1/n) log u_n)`) を提供。**ただし型は `ℕ → ℝ≥0∞ → EReal`** で InformationTheory inline (`ℝ` 値) と型が合わず、bridge cost が高い (在庫 §A-5)
3. **教科書 `\doteq` に対応する単一述語は Mathlib に不在**。在庫 §C の 3 候補 (A=`Tendsto`, B=`IsLittleO`, C=`ExpGrowth`) のうち **候補 B (`(log a − log b) =o[atTop] (·:ℝ)`)** が InformationTheory inline と型がマッチ、`IsLittleO` の代数 (`.add`, `.trans`, `.const_mul_left` 等) を直接活用可能
4. **`InformationTheory/Shannon/AEPRate.lean` (905 行)** は既に I-3 相当の closed-form `N(g, ε')` 抽出 lemma を AEP / channel coding 特化で整備済み (`exp_neg_mul_lt_of_rate`, `channelCoding_E2_lt_of_rate`, `typicalSet_prob_ge_at_N`)。**ゼロからの新規実装ではなく "AEPRate を抽象層に持ち上げる" refactor 視点** が現実的だが、callsite migration は本 I-3 の範囲外 (ユーザー方針 §C-5)
5. **危険箇所**: `IsLittleO.of_tendsto_div_atTop` / `isLittleO_iff_tendsto` は `[NormedField 𝕜]` section で `ℝ≥0∞` 値 sequence では直接使えない (在庫 §D)。`Asymptotics.IsEquivalent.log` は `g → atTop` 必須で `exp(-nD)` 系 (`→ 0`) には逆数経由でしか使えない (在庫 §D)

### 非ゴール

- 既存 `AEPRate.lean` (905 行) の **internal 表現変更 / callsite migration** — しない (ユーザー方針)。既存 `exp_neg_mul_lt_of_rate` 等はそのまま残し、本 I-3 は **抽象 wrapper を追加** するだけで吸収
- **`ExpGrowth` を採用した bridge 実装** — しない (在庫 §C-3 の型ミスマッチ cost が高すぎ)
- **`Tendsto ((1/n) log ...) → -C` 形 inline を `DotEq` に書き換える既存 callsite migration** — しない (本 I-3 で I-3 notation を **追加** するだけ、既存 8 ファイルは regression ゼロ)
- **`DotEq` の `ℝ≥0∞` 値版 alias** — しない (本 I-3 の §C-2 で確定、必要なら別タスクで後付)

---

## B. Approach

**1 ファイル 1 namespace、全部 opt-in な notation + 述語 + closed-form wrapper 層**。既存 `AEPRate.lean` は不変。

```
新規ファイル: InformationTheory/InformationTheory/Asymptotic.lean
namespace : InformationTheory.Asymptotic
中身:
  1. noncomputable def DotEq (a b : ℕ → ℝ) : Prop :=
       (fun n => Real.log (a n) - Real.log (b n)) =o[atTop] (fun n => (n : ℝ))
  2. scoped notation:50 a " ≐ " b => DotEq a b
  3. lemma DotEq.refl / symm / trans / mul / inv             -- IsLittleO 経由で 1〜3 行ずつ
  4. lemma dotEq_iff_tendsto_log_div                          -- (1/n) log (a/b) → 0 形への bridge
  5. theorem exp_decay_N_of_pos (g ε' : ℝ) ...                -- closed-form N extraction
  6. example  -- 動作確認 1 個 (DotEq + exp_decay の組合せ)
```

**「opt-in な notation 層」の意味**: notation は `scoped[InformationTheory.Asymptotic]` で限定 (I-1 と同じ流儀)。`open InformationTheory.Asymptotic` した callsite だけが `a ≐ b` を見る。既存 `AEPRate.lean` や `SanovLDPEquality.lean` 等 8 ファイルは `open` を追加しない限り影響を受けない (regression ゼロを保証)。

**「薄い述語層」の意味**: `DotEq` は 1 行 `def` で Mathlib `IsLittleO` を呼ぶだけ。**新規 bridge lemma は最小限** (`dotEq_iff_tendsto_log_div` 1 本、InformationTheory inline の `Tendsto ((1/n) log ...)` 形と接続するため必須)。`refl`/`symm`/`trans`/`mul`/`inv` 等の基本性質は `IsLittleO` の対応性質 (`IsLittleO.refl`, `.neg`, `.trans`, `.add` 等) を 1〜3 行で叩く。

**closed-form rate extraction wrapper の位置付け**: 既存 `AEPRate.lean:323` の `exp_neg_mul_lt_of_rate` を **AEP/channel coding 非依存** に再定式化 (`exp_decay_N_of_pos`)。本 I-3 で publish するのは **wrapper の存在と署名のみ** で、既存 callsite migration は本タスクの範囲外。後続 seed (T1-B Chernoff, T1-C Cramér) が新規 callsite で `exp_decay_N_of_pos` を使う想定。**もし wrapper 充填中に既存 `exp_neg_mul_lt_of_rate` と signature が完全一致できず統合困難**と判明したら、撤退ライン §H-1 に従い本 I-3 は wrapper を含めず notation + `DotEq` def + 基本性質のみで close。

**bridge lemma の追加方針**: 在庫 §C-2 で示した `dotEq_iff_tendsto_log_div` (1 本) のみ確実に追加。それ以外は Phase 3 のサンプル `example` 実装中に必要と判明した時のみ 1〜2 本追加。**4 本以上**必要になったら撤退ライン §H-3 を発動。

---

## C. 設計判断 (確定)

> 在庫 §C, §D + textbook-roadmap §I-3 + 同 family 前例 (I-1 `typed-rv-plan.md`) に基づく。各項目は **plan 起草時点で確定**、Phase 2 / 3 で実装時に動揺したら判断ログに append する。

### C-1. `\doteq` の表現方式 → **候補 B (`IsLittleO`) 確定**

**確定**: `DotEq a b := (Real.log ∘ a − Real.log ∘ b) =o[atTop] (·:ℝ)` の **候補 B** を採用。

理由 (在庫 §C-2 比較を再評価):

- **InformationTheory inline と型がマッチ**: 既存 8 ファイルは全て `a, b : ℕ → ℝ` 形で書かれており、`Real.log` の差を `IsLittleO` する形は **値域 `ℝ` のまま**で済む。候補 C (`ExpGrowth`) は `ℝ≥0∞ → EReal` の型変換 bridge が必要で cost が高い (在庫 §C-3)
- **Mathlib API の代数が直接使える**: `IsLittleO.add`, `.sub`, `.const_mul_left`, `.trans` 等で `DotEq` の `refl`/`symm`/`trans`/`mul` (`a₁·a₂ ≐ b₁·b₂` if `a_i ≐ b_i`) / `inv` (`1/a ≐ 1/b` if `a ≐ b`) を **1〜3 行**で割れる
- **候補 A (`Tendsto ((1/n) log (a/b)) → 0`) に対する優位**: 候補 A は `IsLittleO` 代数を使えず、`refl`/`symm`/`trans` を全部 `Tendsto` 補題 (`Tendsto.add`, `Tendsto.neg`) で書く必要があり手間が多い。**候補 A は in-essence "候補 B + 1 本 bridge" に等しく**、`dotEq_iff_tendsto_log_div` 1 本で同値性は確保される
- **候補 C (`ExpGrowth`) に対する優位**: `ExpGrowth` は新規 (2025) で Mathlib 内 callsite が限定的、`ℝ≥0∞`/`EReal` 経由 bridge が 30〜50 行追加で必要。本 I-3 を 80〜150 行に収める観点で却下

**前提条件の取り扱い**: 「`Real.log` は `x ≤ 0` で `0`」(在庫 §D) の事故は **述語の中には組み込まない**。`DotEq a b` は `a n ≤ 0` でも well-defined (定義上は `Real.log (a n) = 0` で `IsLittleO` 不等式が成立しがち)。textbook での `\doteq` は通常 `a_n, b_n > 0` 文脈で使われるが、**positivity hypothesis は呼び出し側で渡す** (`hPos : ∀ n, 0 < a n ∧ 0 < b n` を `dotEq_iff_tendsto_log_div` 等の bridge lemma に明示要求)。これにより `DotEq` 自体は型のみで決まり、positivity は use site で扱う設計。

**`a → 0` 系の取り扱い**: `exp(-nD)` 形 (`→ 0`) は `Real.log` で `-∞` ではなく `0` に潰れる Mathlib 規約のため、教科書通り扱うには `-Real.log` を `+∞` 側 (`log (1/a)`) で見る必要がある。**`DotEq` の定義段階では吸収せず**、必要なら use site で `Real.log_inv` を経由する。

### C-2. 値域 → **`ℝ` 値主、`ℝ≥0∞` 値 alias は publish しない**

**確定**: `DotEq (a b : ℕ → ℝ)` の **`ℝ` 値版のみ** を採用、publish する。

理由:

- InformationTheory inline 8 ファイルは **全て `ℝ` 値** で書かれている (在庫 §B: `μ.real {x}`, `(klDiv P Q).toReal`, `(...:ℝ).toReal`, `Real.exp (-(n:ℝ) * D)`)
- `klDiv : ℝ≥0∞` 直で扱う場面 (`klDiv P Q < ∞` で `.toReal` を取らない) は **Stein / StrongStein では rate 部分のみ `.toReal` で `ℝ` に降ろしてから `Tendsto` する** 慣習が確立済み (在庫 §B #4)
- `ℝ≥0∞` 値の `DotEq₂ (a b : ℕ → ℝ≥0∞)` を将来必要としたら、`DotEq a.toReal b.toReal + 有限性仮定` の形で 1 行 `abbrev` を後付で追加すれば良い。互換性は保たれる
- I-1 `typed-rv-plan.md` §C-1 と同じ「1 形のみ publish、`₂` 版は後付」方針と整合

### C-3. notation → **`≐` (U+2250) を `scoped[InformationTheory.Asymptotic]` で precedence 50**

**確定**:

- **scope**: `scoped[InformationTheory.Asymptotic] notation:50 a " ≐ " b => DotEq a b` で限定。I-1 の `H(X)` 等と同じ流儀
- **precedence**: 50 (Mathlib `IsEquivalent` の `~[l]` notation precedence と同じ、在庫 §A-7)
- **kind**: `notation` (`notation3` は不要、`DotEq` には暗黙 placeholder がないため)
- **記号選定**: `≐` (U+2250 APPROACHES THE LIMIT)。教科書 Cover-Thomas の `\doteq` (TeX `\doteq` = `≐`) と同じ Unicode コードポイント。1 文字 `=` や `≡` との衝突なし
- **Mathlib `Asymptotics` notation を破壊しない**: `=O[l]`, `=o[l]`, `=Θ[l]`, `~[l]` はすべて中置 precedence 100 または 50、`≐` は別 token なので衝突しない (在庫 §A-7)
- **1 文字 `≐` の衝突確認は Phase 3 着手時点で `rg`/`loogle` で行う**。衝突が見つかった場合は撤退ライン §H-2 で対応 (`≐[atTop]` 形に縮退)

### C-4. `o(n)` notation → **Mathlib `=o[atTop]` 直書き、新規 notation 追加しない**

**確定**: 教科書 `o(n)` は **Mathlib `=o[atTop] (fun n => (n:ℝ))` の直書きで通す**。新規 notation は追加しない。

理由:

- Mathlib `=o[l]` notation は **大域 + precedence 100**、すでに完成度が高い (在庫 §A-7)
- `notation:50 f " =o(n)" => f =o[atTop] (fun n : ℕ => (n : ℝ))` のような略記を追加すると、Lean parser での衝突可能性 + 既存 Mathlib callsite との見た目不一致を招く
- 教科書本文では「`f(n) = o(n)`」と書くが、Lean では `f =o[atTop] (·:ℝ)` で **完全に意味保存**、書き味の差は小さい
- I-1 `typed-rv-plan.md` で「束ねクラスを作らない、Mathlib 慣習維持」と決めたのと同じ思想

**docstring で代替**: `InformationTheory/InformationTheory/Asymptotic.lean` の冒頭 docstring で「教科書 `f(n) = o(n)` は Lean では `f =o[atTop] (fun n : ℕ => (n : ℝ))` で書ける、`o(1)` は `f =o[atTop] (fun _ => (1 : ℝ))`」と例示する (在庫 §A-7 末尾)。

### C-5. `AEPRate.lean` との関係 → **既存はそのまま残し、I-3 で抽象 wrapper を追加**

**確定**: `AEPRate.lean` (905 行) は **internal 表現も既存 lemma 名 (`exp_neg_mul_lt_of_rate` 等) も完全に不変**。本 I-3 で追加するのは:

- 抽象 wrapper `exp_decay_N_of_pos (g ε' : ℝ) (hg : 0 < g) (hε' : 0 < ε') : ∃ N, ∀ n ≥ N, Real.exp (-(n:ℝ) * g) < ε'`
- (任意) `AEPRate.exp_neg_mul_lt_of_rate` を呼び替える 1 行 alias (`exp_decay_N_of_pos := AEPRate.exp_neg_mul_lt_of_rate`)

callsite migration (`AEPRate.exp_neg_mul_lt_of_rate` → `Asymptotic.exp_decay_N_of_pos` の使い替え) は **本 I-3 の範囲外**。後続 seed (T1-B Chernoff 等) が新規 callsite で `exp_decay_N_of_pos` を使う。既存 `AEPRate.lean` 内部 + 既存 7 ファイル callsite (`RateDistortionAchievabilityPhaseEStrongFinal`, `TwoSidedExtension`, `SanovLDPEquality`, `BirkhoffErgodic`, `ConditionalMethodOfTypes` 等、在庫 §E-3) はそのまま残す。

選択肢 (ii) 「`AEPRate` 既存 lemma を I-3 wrapper から呼び替え」は **採用しない** (callsite migration 不要、regression リスクゼロ、ユーザー方針 §C-5 既存 callsite 不変と整合)。

### C-6. exponent extraction wrapper の引数形 → **`(g : ℝ) (ε' : ℝ) (hg : 0 < g) (hε' : 0 < ε')` 形**

**確定**: wrapper signature:

```lean
/-- Closed-form `N` for `exp(-n·g) < ε'`: for any `g, ε' > 0`, there exists
`N := ⌈max 0 (-Real.log ε' / g)⌉ + 1` such that for all `n ≥ N`, `Real.exp (-(n:ℝ) * g) < ε'`. -/
theorem exp_decay_N_of_pos {g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N, Real.exp (-(n : ℝ) * g) < ε'
```

理由:

- 引数名 `g`, `ε'` は **既存 `AEPRate.exp_neg_mul_lt_of_rate` の引数名と一致** (在庫 §B #9)。既存ファイルの proof-log や docstring と整合
- 暗黙引数 `{g ε' : ℝ}` で書くことで `(hg : 0 < g)` のみから type 推論可能 (Mathlib 慣習)
- 「`g`, `ε'` の名前は family ごとに違うため、抽象側の名前は中立 (`r`, `c`) にする方がよい」と在庫 §E-3 で示唆されているが、**抽象側を `r`, `c` にすると既存 `AEPRate` callsite との連続性が切れる**ため、本 plan では `g`, `ε'` を維持する

**追加 wrapper の候補** (Phase 3 で必要と判明したら追加):

- `channelCoding_E2_lt_of_pos` (在庫 §B #10 の抽象化、より複雑な指数形): **本 I-3 範囲外**、撤退ライン §H-1 で対応
- `tendsto_to_metric_N` (`Tendsto u atTop (𝓝 c)` から `∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε` 抽出): Mathlib `Metric.tendsto_atTop` で十分 (在庫 §A-4)、本 I-3 で wrapper 追加しない

---

## D. ファイル / モジュール配置

### 新規ファイル

**`InformationTheory/InformationTheory/Asymptotic.lean`** (80〜150 行見込み)

**配置先選択**: I-1 が `InformationTheory/Shannon/TypedRV.lean` (Shannon 配下) だったのに対し、I-3 は **`InformationTheory/InformationTheory/Asymptotic.lean` (InformationTheory 配下)** を採用。

理由:

- I-3 の `DotEq` / `exp_decay_N_of_pos` は **Shannon 専用ではなく、Sanov LDP / channel coding / rate distortion / Stein / Chernoff 等の幅広い情報理論 family に渡る汎用 wrapper**。`Shannon/` 配下に置くと「Shannon 系専用」と誤解される
- `InformationTheory/InformationTheory/` 配下は **既存に類似の汎用層がない**ため、新規 namespace `InformationTheory.Asymptotic` を切る
- 後続 seed (T2-A AWGN, T3-B MAC, T4-A LZ78) が `open InformationTheory.Asymptotic` 1 行で取り込めるよう、Shannon 階層から独立した位置に置く

`InformationTheory.lean` (library root) に追記:

```lean
import InformationTheory.InformationTheory.Asymptotic
```

### import 一覧 (在庫 §G 参照、`import Mathlib` 禁止)

```lean
import Mathlib.Analysis.Asymptotics.Defs              -- IsLittleO, IsBigO, =o[atTop]
import Mathlib.Analysis.Asymptotics.Lemmas            -- isLittleO_iff_tendsto, natCast_atTop, of_tendsto_div_atTop
import Mathlib.Analysis.SpecialFunctions.Log.Basic    -- Real.log, log_div, log_le_log_iff, isLittleO_log_id_atTop
import Mathlib.Analysis.SpecialFunctions.Exp          -- Real.exp_lt_iff, Real.exp_le_exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real     -- Real.exp_mul (rpow)
import Mathlib.Topology.MetricSpace.Pseudo.Defs       -- Metric.tendsto_atTop (任意)
```

**Asymptotics 系 import の取捨選択**:

- `Mathlib.Analysis.Asymptotics.AsymptoticEquivalent` は **不要** (本 I-3 で `~[l]` notation を使わない、`DotEq` は `IsLittleO` 直書き)
- `Mathlib.Analysis.Asymptotics.SpecificAsymptotics` は **不要** (`IsEquivalent.log` を使わない)
- `Mathlib.Analysis.Asymptotics.ExpGrowth` は **不要** (候補 C 不採用、§C-1)
- `Mathlib.Topology.Order.LiminfLimsup` は **不要** (sandwich → `Tendsto` は use site で対応、本 I-3 で wrapper 化しない)

import 6 個で済む見込み。Phase 1 着手時に **silent check** で確認、追加が必要なら 1〜2 個追加可。

### namespace

**`InformationTheory.Asymptotic`** (新規)。notation `≐` は同 namespace で `scoped` 修飾。

---

## E. Phase 1 — skeleton (sorry-driven 出だし)

> 全項目を `:= by sorry` (notation は宣言だけ) で書き、`lake env lean InformationTheory/InformationTheory/Asymptotic.lean` が **silent + sorry warning のみ** になることを Phase 1 の Done 条件とする。

```lean
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Asymptotic / exponent framework

Textbook (Cover-Thomas) `a_n ≐ b_n` (exponent equality) と closed-form rate extraction
wrapper を提供する I-3 層。

## 表記法

- `a ≐ b` (`DotEq a b`): `(Real.log ∘ a − Real.log ∘ b) =o[atTop] (·:ℝ)`
- 教科書 `f(n) = o(n)` は Lean では `f =o[atTop] (fun n : ℕ => (n : ℝ))` で書ける
- 教科書 `f(n) = o(1)` は Lean では `f =o[atTop] (fun _ => (1 : ℝ))` で書ける
-/

namespace InformationTheory.Asymptotic

open Asymptotics Filter Topology Real

/-- **Exponent equality (textbook `\doteq`)**: `a_n ≐ b_n` if
  `Real.log (a n) − Real.log (b n) = o(n)` along `atTop`.

  教科書 (Cover-Thomas) の `a_n ≐ b_n ⟺ (1/n) log (a_n / b_n) → 0` と同値
  (`dotEq_iff_tendsto_log_div`, under positivity `0 < a n ∧ 0 < b n`). -/
def DotEq (a b : ℕ → ℝ) : Prop :=
  (fun n : ℕ => Real.log (a n) - Real.log (b n)) =o[atTop] (fun n : ℕ => (n : ℝ))

@[inherit_doc] scoped notation:50 a " ≐ " b => DotEq a b

/-- `DotEq` is reflexive. -/
lemma DotEq.refl (a : ℕ → ℝ) : a ≐ a := by sorry

/-- `DotEq` is symmetric. -/
lemma DotEq.symm {a b : ℕ → ℝ} (h : a ≐ b) : b ≐ a := by sorry

/-- `DotEq` is transitive. -/
lemma DotEq.trans {a b c : ℕ → ℝ} (hab : a ≐ b) (hbc : b ≐ c) : a ≐ c := by sorry

/-- Multiplicative compatibility: `a₁ * a₂ ≐ b₁ * b₂` if `a_i ≐ b_i` (under positivity). -/
lemma DotEq.mul {a₁ a₂ b₁ b₂ : ℕ → ℝ}
    (hPos₁ : ∀ n, 0 < a₁ n ∧ 0 < b₁ n) (hPos₂ : ∀ n, 0 < a₂ n ∧ 0 < b₂ n)
    (h₁ : a₁ ≐ b₁) (h₂ : a₂ ≐ b₂) :
    (fun n => a₁ n * a₂ n) ≐ (fun n => b₁ n * b₂ n) := by sorry

/-- Inverse compatibility: `1/a ≐ 1/b` if `a ≐ b` (under positivity). -/
lemma DotEq.inv {a b : ℕ → ℝ} (hPos : ∀ n, 0 < a n ∧ 0 < b n) (h : a ≐ b) :
    (fun n => (a n)⁻¹) ≐ (fun n => (b n)⁻¹) := by sorry

/-- **Bridge**: `DotEq` is equivalent to `Tendsto ((1/n) * log (a/b)) → 0`
  under positivity. -/
lemma dotEq_iff_tendsto_log_div (a b : ℕ → ℝ) (hPos : ∀ n, 0 < a n ∧ 0 < b n) :
    a ≐ b ↔
    Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (a n / b n)) atTop (𝓝 0) := by sorry

/-- **Closed-form `N` for `exp(-n·g) < ε'`** (rate extraction wrapper).
  For `g, ε' > 0`, the witness `N := ⌈max 0 (-Real.log ε' / g)⌉ + 1` works.

  既存 `AEPRate.exp_neg_mul_lt_of_rate` の family-agnostic 版。本 I-3 では abstract wrapper
  のみ publish、既存 callsite migration は本タスク範囲外。 -/
theorem exp_decay_N_of_pos {g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N, Real.exp (-(n : ℝ) * g) < ε' := by sorry

end InformationTheory.Asymptotic
```

**各項目で参照する既存補題 (在庫 §A〜D)**:

| 項目 | 既存定義 / 補題 | file:line |
|---|---|---|
| `DotEq` def | `Asymptotics.IsLittleO`, `Real.log` | `Mathlib/Analysis/Asymptotics/Defs.lean:187`, `Log/Basic.lean` |
| `DotEq.refl` | `IsLittleO.refl_left` (zero function `=o[l] _`) または `(0 : ℕ → ℝ) =o[l] _` 直 | `Mathlib/Analysis/Asymptotics/Defs.lean` (`isLittleO_zero` or similar) |
| `DotEq.symm` | `IsLittleO.neg_left` (`-f =o[l] g ↔ f =o[l] g`) + 引き算交換 | `Mathlib/Analysis/Asymptotics/Defs.lean` |
| `DotEq.trans` | `IsLittleO.add` (微妙、`(log a - log b) + (log b - log c) = (log a - log c)`) | `Mathlib/Analysis/Asymptotics/Defs.lean` |
| `DotEq.mul` | `Real.log_mul` で `log (a₁·a₂) = log a₁ + log a₂` に展開 + `IsLittleO.add` | `Log/Basic.lean:132` |
| `DotEq.inv` | `Real.log_inv` で `log (1/a) = -log a` に展開 + `IsLittleO.neg_left` | `Log/Basic.lean` |
| `dotEq_iff_tendsto_log_div` | `Real.log_div` + `isLittleO_iff_tendsto'` (`g = (·:ℝ)` 限定形) | `Log/Basic.lean:137`, `Asymptotics/Lemmas.lean:382` |
| `exp_decay_N_of_pos` | `AEPRate.exp_neg_mul_lt_of_rate` を移植 | `InformationTheory/Shannon/AEPRate.lean:323` |

**bridge ヘルパー (新規追加分)**: ゼロ件想定。在庫 §A〜D で確認した Mathlib API + 既存 `AEPRate.lean` 内コードで `exp_decay_N_of_pos` 含めて全て出る。**Phase 3 のサンプル `example` で 1 本足りないと判明したら、そこで追加判断する**。

---

## F. Phase 切り分け

### Phase 1: skeleton + silent

- 上記 E の内容を `InformationTheory/InformationTheory/Asymptotic.lean` に Write
- `InformationTheory.lean` に `import InformationTheory.InformationTheory.Asymptotic` 追記
- `lake env lean InformationTheory/InformationTheory/Asymptotic.lean` が silent + sorry warning のみ
- **proof-log**: no (skeleton 段階)
- 工数: 30 分

### Phase 2: 基本性質充填 (`DotEq.refl` / `symm` / `trans` / `mul` / `inv`)

- `DotEq.refl`: `Real.log a − Real.log a = 0` → `IsLittleO.zero_left` (または `IsLittleO.zero` 直)
- `DotEq.symm`: `Real.log b − Real.log a = −(Real.log a − Real.log b)` → `IsLittleO.neg_left`
- `DotEq.trans`: `(log a − log b) + (log b − log c) = (log a − log c)` → `IsLittleO.add`
- `DotEq.mul`: `Real.log (a₁·a₂) = Real.log a₁ + Real.log a₂` (`log_mul`, positivity 必須) で展開 → `IsLittleO.add`
- `DotEq.inv`: `Real.log a⁻¹ = -Real.log a` (`log_inv`) で展開 → `IsLittleO.neg_left` + `IsLittleO.neg_right`
- 工数: 30〜45 分 (各 lemma 5〜10 行、`positivity` / `linarith` / `ring` で割れる予定)
- **proof-log**: no
- Done: `lake env lean InformationTheory/InformationTheory/Asymptotic.lean` が silent、`DotEq.refl`/`symm`/`trans`/`mul`/`inv` の 5 つ全てが sorry-free

### Phase 3: bridge + closed-form wrapper + サンプル `example`

- **3-α**: `dotEq_iff_tendsto_log_div` 充填:
  - `→` 方向: `IsLittleO` から `Tendsto ((log a − log b) / n) → 0` (`isLittleO_iff_tendsto'`), `Real.log_div` で `log a − log b = log (a/b)` に rewrite (positivity 必須)
  - `←` 方向: 逆方向、`Tendsto ((1/n) * log (a/b)) → 0` → `IsLittleO`
  - 工数: 30〜45 分
- **3-β**: `exp_decay_N_of_pos` 充填:
  - 既存 `AEPRate.exp_neg_mul_lt_of_rate` (`InformationTheory/Shannon/AEPRate.lean:323`) の証明をコピー + family-agnostic に名前を中立化 (`g`, `ε'` は維持、§C-6)
  - `N := ⌈max 0 (-Real.log ε' / g)⌉ + 1` を witness、`Real.exp_lt_iff_lt_log` 等で割る
  - 工数: 20〜30 分 (既存 30 行のコピー + 名前修正)
- **3-γ**: notation 衝突確認 + 動作確認 `example`:
  - `rg "\"≐\"" .lake/packages/mathlib/Mathlib | head` で衝突確認
  - 衝突なし → notation はそのまま、`example` 1 個書く:

```lean
example (a b : ℕ → ℝ) (hPos : ∀ n, 0 < a n ∧ 0 < b n)
    (h : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (a n / b n)) atTop (𝓝 0)) :
    a ≐ b := (dotEq_iff_tendsto_log_div a b hPos).mpr h

example {g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N, Real.exp (-(n : ℝ) * g) < ε' :=
  exp_decay_N_of_pos hg hε'
```

  - 衝突あり → 撤退ライン §H-2 (`≐[atTop]` 形に縮退)
- 工数: 30〜45 分 (3-γ 全体)
- **proof-log**: yes (notation 衝突有無 / `exp_decay_N_of_pos` の signature が `AEPRate` 既存と一致したか / bridge lemma の `→`/`←` 方向で詰まった箇所を記録)
- Done: `lake env lean InformationTheory/InformationTheory/Asymptotic.lean` silent、`DotEq.refl`/`symm`/`trans`/`mul`/`inv`/`dotEq_iff_tendsto_log_div`/`exp_decay_N_of_pos` の **7 つ全て + 2 つの `example` が elaborate に通る**

### Phase 4: verify + regression check

- `lake env lean InformationTheory/InformationTheory/Asymptotic.lean` 0 error / 0 sorry / warning 最小
- 既存 0 sorry ファイルへの **regression なし**を確認:
  - `lake env lean InformationTheory/Shannon/AEPRate.lean` silent (本 I-3 が `AEPRate` を import せずに済むことの確認、本 plan §D で `AEPRate` を import 候補から除外済み)
  - `lake env lean InformationTheory/Shannon/AEP.lean` silent
  - `lake env lean InformationTheory/Shannon/SanovLDPEquality.lean` silent
  - `lake env lean InformationTheory/Shannon/StrongStein.lean` silent
  - `lake env lean InformationTheory/Shannon/SMBAlgoetCover.lean` silent
  - `lake env lean InformationTheory/Shannon/EntropyRate.lean` silent
- (必要なら `lake build InformationTheory.InformationTheory.Asymptotic` で olean 焼き)
- 工数: 15〜30 分
- **proof-log**: yes (合流 + メトリクス: 行数 / 新規 def 数 / 基本性質 lemma 数 / 衝突確認した識別子のメモ)
- Done: 全ファイル silent、proof-log 完備

**~~Phase 5 (callsite migration / 既存 inline 表現の `DotEq` 書き換え)~~** — 本タスクの範囲外 (ユーザー方針 §C-5)。後続 seed (T1-B Chernoff, T1-C Cramér, T2-A AWGN, T3-B MAC, T4-A LZ78 等) が自身の callsite で `open InformationTheory.Asymptotic` する形で取り込む。既存 8 ファイル inline は不変。

---

## G. 判定条件 (Definition of Done)

1. `lake env lean InformationTheory/InformationTheory/Asymptotic.lean` が **0 error / 0 sorry / 警告最小** で silent
2. **`DotEq` の `refl`/`symm`/`trans`/`mul`/`inv` 5 つすべてが動く** — Phase 2 充填済み
3. **`dotEq_iff_tendsto_log_div` + `exp_decay_N_of_pos` が動く** — Phase 3 充填済み
4. **notation `≐` が elaborate に通る** — Phase 3 末尾の `example` で 2 つの notation 使用箇所が silent
5. **既存 0 sorry ファイルが regression なし** — 上記 §F Phase 4 の 6 ファイル + `InformationTheory/Shannon/Stein.lean` 等が `lake env lean` で silent
6. `InformationTheory.lean` に `import InformationTheory.InformationTheory.Asymptotic` 追記済み
7. proof-log (`docs/proof-log-asymptotic.md` 等) に **Phase 3 で確認した衝突有無 / `exp_decay_N_of_pos` の AEPRate との signature 一致確認 / 最終 lemma 名一覧 verbatim** を記録

---

## H. 撤退ライン

> 在庫 §F の 4 候補を本 plan に取り込み、Phase 2 / 3 着手時に顕在化しうるリスクを 4 つ列挙して撤退条件を確定する。

### H-1. **`exp_decay_N_of_pos` 充填中に既存 `AEPRate.exp_neg_mul_lt_of_rate` と signature が完全一致できない / 統合困難**

- 判定: Phase 3-β で `AEPRate.exp_neg_mul_lt_of_rate` の証明 30 行を移植中に、引数順 / `Nat.ceil` 境界処理 / `g, ε'` の `> 0` 仮定の取り方が微妙にズレ、family-agnostic 化に 3 回以上の試行が必要
- 撤退: **本 I-3 から `exp_decay_N_of_pos` を除外**し、wrapper は本タスク範囲外として後続 seed (T1-B Chernoff など) に委ねる。本 I-3 は **notation + `DotEq` def + 基本性質 (5 個) + `dotEq_iff_tendsto_log_div` (1 個) のみ**で close。規模は 60〜100 行に縮減
- 工数影響: -30 分 (`exp_decay_N_of_pos` 充填の 30 分を節約)

### H-2. **`≐` notation が Mathlib / Std で衝突**

- 判定: Phase 3-γ 着手時 `rg "\"≐\"" .lake/packages/mathlib/Mathlib` または `loogle "≐"` で衝突を発見、または notation 投入後 `lake env lean` でパースエラー
- 撤退: 縮退選択肢を順に試す:
  1. **`≐[atTop]` 形** (Mathlib `~[l]` precedent、filter 明示)。`scoped notation:50 a " ≐[" l "] " b => DotEq a b (filter := l)` のような形
  2. **`DotEq a b` predicate 形のみ** (notation を全廃)
  3. **ASCII 形** `=. [atTop] =` 等 (在庫 §F 末尾の提案)
- 縮退判定は **Phase 3-γ 開始時に確定**して proof-log に記録。途中で 1 → 2 → 3 と滑らせない (確定後は固定)
- 工数影響: +30 分 (縮退選択 + 既存 docstring の書き直し)

### H-3. **`DotEq` の `refl`/`symm`/`trans` を充填中、`IsLittleO` 代数で予期しない型クラス要求が発生**

- 判定: Phase 2 で `DotEq.refl` を `IsLittleO.refl_left` で割ろうとして `[NormedField ℝ]` 等の予期しない instance 要求、または `0 =o[l] g` 形と `(0 : ℕ → ℝ) =o[l] _` 形のマッチで詰まる
- 撤退: **`DotEq` を直接展開**して `simp [DotEq]` + `IsLittleO.refl_left` で割る形に書き直す。それでも詰まる場合は **基本性質 (`refl`/`symm`/`trans`) のみ手書きで `Asymptotics.IsLittleO.def` から `∀ ε > 0, ∀ᶠ n, ...` を引き出す形で証明** (5〜15 行/lemma に膨張)。`mul`/`inv` は positivity hypothesis 要求が強く落とし穴が多いため、撤退ライン H-1 と併発した場合は **`mul`/`inv` も本 I-3 から除外**して 60〜80 行で close
- 工数影響: +30〜60 分

### H-4. **bridge lemma が `dotEq_iff_tendsto_log_div` 以外に 1 本以上必要だと判明** (Phase 3-γ の `example` で詰まる)

- 判定: Phase 3-γ のサンプル `example` を 1 つも書けない (notation 展開後に `dotEq_iff_tendsto_log_div` だけでは割れない)
- 撤退: **本タスクの範囲を「`DotEq` + 基本性質 + `dotEq_iff_tendsto_log_div` + 必要 bridge 1〜3 本」に拡大**し、必要 bridge を 1〜3 本だけ追加して Phase 4 を再評価する。**4 本以上必要**になった場合は I-3 を Phase A (notation + def + 基本性質) / Phase B (bridge lemma 群) に分割、本 plan は Phase A までで close + Phase B を別 plan に切り出す
- 工数影響: +30 分〜+2 時間

---

## I. 規模見積もり

| 指標 | 見積もり |
|---|---|
| 新規 Lean 行数 | 80〜150 行 (1 ファイル) |
| 新規 `def` 数 | 1 (`DotEq`) |
| 新規 `lemma` 数 (基本性質) | 5 (`refl`, `symm`, `trans`, `mul`, `inv`) |
| 新規 `lemma` 数 (bridge) | 1 (`dotEq_iff_tendsto_log_div`) |
| 新規 `theorem` 数 (wrapper) | 1 (`exp_decay_N_of_pos`) |
| 新規 notation 数 | 1 (`≐`) |
| サンプル `example` 数 | 2 (`dotEq_iff_tendsto_log_div.mpr` 経由 + `exp_decay_N_of_pos` 直呼) |
| ターン見積もり | 1〜2 セッション (Phase 1 + 2 で 1 セッション、Phase 3 + 4 でもう 1 セッション) |
| 実装時間 | 1.5〜3 時間 (Phase 1: 30 分、Phase 2: 30〜45 分、Phase 3: 80〜120 分、Phase 4: 15〜30 分、撤退ライン発動時 +30 分〜+1 時間) |
| 撤退ライン §H-1 (wrapper 除外) 発動時 | -30 分、-20〜30 行 (60〜120 行に縮減) |
| 撤退ライン §H-2 (notation 縮退) 発動時 | +30 分、行数増減なし |
| 撤退ライン §H-3 (基本性質手書き) 発動時 | +30〜60 分、+30〜50 行 |
| 撤退ライン §H-4 (bridge 追加) 発動時 | +30 分〜+2 時間、+10〜50 行 |

**新数学なし**。在庫が示した通り「`DotEq` def + 5 性質 + 1 bridge + 1 wrapper + 1 notation」で本体は終わる。textbook-roadmap 予想 300-500 行より大幅に小さく (在庫 §E-6 でも「80-150 行」見込み)。

---

## J. 後続 seed への影響メモ

### I-3 → T1-B Chernoff Information

`P_e^{(n)} \doteq \exp(-n · C(P_1, P_2))` (textbook-roadmap §T1-B) の statement を Lean で書く際、`P_e^{(n)} ≐ (fun n => Real.exp (-(n:ℝ) * C))` の形で `DotEq` notation がそのまま使える。`exp_decay_N_of_pos` は Chernoff achievability の closed-form `N` 抽出で再利用可。

### I-3 → T1-C Cramér's Theorem

`(1/n) log P[\bar{S}_n ∈ A] → -inf_{x ∈ A} I(x)` (textbook-roadmap §T1-C) は **本 I-3 の `DotEq` の rate 形そのもの**。`P[\bar{S}_n ∈ A] ≐ Real.exp (-(n:ℝ) * inf_{x ∈ A} I(x))` の形で使える。

### I-3 → T2-A AWGN converse

AWGN channel coding の error probability rate (textbook-roadmap §T2-A) で `P_e^{(n)} ≐ Real.exp (-(n:ℝ) * E_AWGN)` 形が使える。`exp_decay_N_of_pos` も achievability 側で再利用。

### I-3 → T3-B MAC converse / T4-A LZ78

MAC error probability rate と LZ78 asymptotic optimality (`L_n / n → H` の form) のいずれも `DotEq` 形で書ける。LZ78 は `entropyRate` (Ch.4 完成済み) との直接連結で `(L_n/n) ≐ entropyRate` などの形を想定。

### I-3 → 既存 8 ファイル (callsite migration)

**本 I-3 の範囲外**。`AEP.lean`, `SMBAlgoetCover.lean`, `StrongStein.lean`, `Stein.lean`, `SanovLDPEquality.lean`, `EntropyRate.lean`, `AEPRate.lean` の inline `Tendsto ((1/n) log ...) → -C` 形は不変。後続 cleanup タスク (新 seed 化、本 I-3 外) で migration を検討する。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-18 起草**: 在庫調査 `asymptotic-mathlib-inventory.md` 完了後の plan 起草。設計判断 §C-1〜6 を確定:
   - C-1 `DotEq` 表現方式 = **候補 B (`IsLittleO`)**: InformationTheory inline (`ℝ` 値) と型がマッチ、Mathlib `IsLittleO` 代数を直接活用。候補 A (`Tendsto`) は in-essence 候補 B + 1 bridge と同等、候補 C (`ExpGrowth`) は `ℝ≥0∞`/`EReal` bridge cost で却下
   - C-2 値域 = **`ℝ` 値主のみ publish**、`ℝ≥0∞` 版 alias は本 I-3 では追加しない (後付可)
   - C-3 notation = **`≐` (U+2250) を `scoped[InformationTheory.Asymptotic]` で precedence 50**。教科書 `\doteq` (TeX) と同じ Unicode、Mathlib `Asymptotics` notation と衝突なし
   - C-4 `o(n)` notation = **Mathlib `=o[atTop]` 直書きのまま**、新規 notation 追加しない (Mathlib 慣習維持、I-1 と同じ思想)
   - C-5 `AEPRate.lean` との関係 = **既存はそのまま残し、I-3 で抽象 wrapper を追加**。既存 callsite migration は本 I-3 範囲外
   - C-6 wrapper signature = **`exp_decay_N_of_pos {g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε') : ∃ N, ∀ n ≥ N, Real.exp (-(n:ℝ) * g) < ε'`**。既存 `AEPRate.exp_neg_mul_lt_of_rate` と引数名一致

   撤退ラインを §H-1〜4 の 4 シナリオで具体化。規模 80〜150 行 / 1〜2 セッション / 1.5〜3 時間。

2. **2026-05-18 実装完了** (`lean-implementer`): Phase 1〜4 を 1 セッションで一気通貫実行、撤退ライン発動なし。
   - **Phase 1 (skeleton)**: 想定通り。1 件のみ調整 — `≐` notation の precedence で `a ≐ b ↔ ...`
     パースエラーが発生 (`Iff b` 型不一致)。`scoped notation:50 a:51 " ≐ " b:51 => DotEq a b`
     のように両オペランドの先取り precedence を 51 に明示して解決。設計判断 §C-3 は維持
     (記号 / scope / precedence 50 の本体は不変)、operand precedence の明示は実装詳細レベル
   - **Phase 2 (基本性質)**: refl / symm / trans / mul / inv 5 件すべて plan §F の方針どおり
     `IsLittleO.zero` / `IsLittleO.neg_left` / `IsLittleO.add` + `Real.log_mul` / `Real.log_inv`
     で 5〜20 行ずつ。**`DotEq.inv` の `hPos` 仮定を削除** — Mathlib `Real.log_inv : log x⁻¹ = -log x`
     が **無条件**で成立 (`x ≤ 0` でも両辺 0)、positivity 不要と判明。設計判断 §C-1 末尾の
     "positivity は use site で扱う" 原則にも整合
   - **Phase 3 (bridge + wrapper)**:
     - `dotEq_iff_tendsto_log_div` は `isLittleO_iff_tendsto'` (`Eventually` 版) を採用。
       `g n = (n:ℝ)` は `n = 0` で 0 になるが、`eventually_gt_atTop 0` で覆って解決
     - `exp_decay_N_of_pos` は plan §C-6 のシグネチャ `{g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε')`
       で確定、既存 `AEPRate.exp_neg_mul_lt_of_rate` の 30 行証明を verbatim 移植
       (witness `N := ⌈max 0 (-Real.log ε' / g)⌉ + 1`)。AEPRate 既存と signature 完全一致、
       撤退ライン §H-1 発動せず
     - `example` 3 個追加 (`dotEq_iff_tendsto_log_div.mpr`, `exp_decay_N_of_pos`, `DotEq.refl`)
   - **Phase 4 (regression)**: `AEP.lean` / `AEPRate.lean` / `SanovLDPEquality.lean` /
     `StrongStein.lean` / `SMBAlgoetCover.lean` / `EntropyRate.lean` 全て `lake env lean` silent。
     `AEP.lean` には既存の `unusedSectionVars` linter warning が残るが I-3 とは無関係 (pre-existing)
   - **規模**: 195 行 (plan 見積 80〜150 行を僅かに超過、追加分は example 3 個 + docstring 拡張 + bridge の `h_ratio_eq` 補助式)
   - **bridge lemma 追加**: 1 本のみ (`dotEq_iff_tendsto_log_div`)。§H-4 (4 本以上で plan 分割) は発動せず
   - **notation 衝突確認**: `rg -tlean '≐' .lake/packages/mathlib` は `UnicodeLinter.lean:75`
     の allowlist エントリのみ (notation 用途は無し)。衝突なし

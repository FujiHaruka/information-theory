# Shannon コード (B-8) ムーンショット計画 🌙

> 実態整合 (2026-05-20): DONE-UNCOND — `shannonCode_expected_length_bounds` (`Common2026/Shannon/ShannonCode.lean:345`) ほか `shannonLength_kraft_le_one` `:129`、`entropyD_le_expectedLength_of_kraft` `:164`、`expectedLength_shannon_lt_entropyD_add_one` `:261` が 0 sorry で publish。標準 typeclass binder のみ、pass-through / `Prop := True` 不在。

> Status (2026-05-12): **完了 ✅** (期待長 sandwich、語長水準)。シードカード [B-8](../moonshot-seeds.md#b-追加-2026-05-11-起草既存-5-シード--b-1b-4-を踏まえた後続) を膨らませた本命。**Kraft 逆向き (prefix code 存在構成) は別 plan で完了**: [shannon-code-kraft-reverse-plan.md](shannon-code-kraft-reverse-plan.md) (B-8', `Common2026/Shannon/ShannonCodeKraftReverse.lean` 498 行、Shannon-Fano D-進数構成)。

## 進捗

- [x] Phase 0 — Mathlib + 既存 Common2026 API インベントリ ✅ → [`shannon-code-mathlib-inventory.md`](shannon-code-mathlib-inventory.md)
- [x] Phase A — D-ary entropy `entropyD` + Shannon 語長 `shannonLength` + 期待長 `expectedLength` 定義
- [x] Phase B — Shannon 語長の Kraft 充足 `shannonLength_kraft_le_one`: `Σ D^{-l(a)} ≤ 1`
- [x] Phase C — 期待長下界 `entropyD_le_expectedLength_of_kraft`: 任意 lengths が Kraft 充足 ⟹ `H_D(P) ≤ E[L]` (Gibbs)
- [x] Phase D — 期待長上界 `expectedLength_shannon_lt_entropyD_add_one`: Shannon 語長で `E[L] < H_D(P) + 1`
- [x] Phase E — sandwich corollary `shannonCode_expected_length_bounds`: 統合主定理 `H_D ≤ E[L_Shannon] < H_D + 1`

## ゴール / Approach

**最終到達点**: 有限アルファベット `X` 上の確率分布 `P` に対し、D-ary alphabet 上の Shannon 語長
`l(x) := ⌈-log_D P(x)⌉ : ℕ` で期待長が `H_D(P) ≤ E[L] < H_D(P) + 1` を達成することの形式化。
Cover-Thomas 5.4-5.5 / 5.8.1。

**Approach の中核 (3 段)**:

1. **(a) Kraft 充足 (順向き経路)**: Shannon 語長は `l(a) ≥ -log_D P(a)` から `D^{-l(a)} ≤ P(a)`、
   よって `Σ D^{-l(a)} ≤ Σ P(a) = 1`。これにより `kraft_mcmillan_inequality` を **逆向きには使わず**、
   「Shannon 語長は Kraft 充足する」事実だけで achievability 側を完結させる。
2. **(b) 期待長下界 (Gibbs 不等式)**: 任意 lengths `l : α → ℕ` が Kraft 充足 `Σ D^{-l(a)} ≤ 1` なら、
   `H_D(P) - E[L] = Σ P(a) · log_D (D^{-l(a)} / P(a)) ≤ logD (Σ D^{-l(a)}) ≤ logD 1 = 0` (Jensen)。
   実装は **logD は monotonic + Real.log_le_sub_one_of_pos** 経路で Jensen 回避: 各項に
   `log_D(D^{-l(a)} / P(a)) ≤ (1/log D) · (D^{-l(a)} / P(a) - 1)` を使い、`P(a)` で乗じて Σ。
3. **(c) 期待長上界 (Shannon 語長の `⌈⌉` 上界)**: `l(a) = ⌈-log_D P(a)⌉ < -log_D P(a) + 1`、
   `P(a)` で乗じて Σ。

**Mathlib に既存 prefix code API は無いことを Phase 0 で確認** (`Mathlib.InformationTheory.Coding.{UniquelyDecodable, KraftMcMillan}` のみ、prefix code 構造体 / `kraft_mcmillan_converse` は無い)。
よって本シードは **「Shannon code 語長は Kraft 不等式を充足し、期待長 sandwich を達成する」** という、
prefix code の **存在を仮定しない、語長水準** の形式化に絞る。Kraft 逆向き (prefix code 構成) は
**B-8' に切り出し** (将来、Mathlib 側に prefix code structure が入れば再着手)。

**撤退ライン**: Phase B-D 緑通過時点で完成。Mathlib 側 `kraft_mcmillan_inequality` は文字列符号
(`Finset (List α)`) 表現を取るが、本シードは語長 (`α → ℕ`) 水準で十分なため、
Mathlib の符号 → 語長の bridge は本シードでは不要。

**ファイル構成**:

```
Common2026/Shannon/
  ShannonCode.lean   ← 全部
```

## Phase 0 - Mathlib + 既存 API インベントリ ✅

- 結果は [`shannon-code-mathlib-inventory.md`](shannon-code-mathlib-inventory.md)。
- 重要な結論:
  - Mathlib `kraft_mcmillan_inequality` は `Finset (List α)` 表現 (語長水準ではなく文字列符号水準)。本シードでは語長水準で完結するため **使わない**。
  - Mathlib に prefix code 構造体は **無い**。`UniquelyDecodable` のみ。
  - `Real.logb` (base-D log) と `Nat.ceil_lt_add_one`, `Nat.le_ceil` (`⌈⌉` の bounds) を主に使う。
  - `Real.log_le_sub_one_of_pos` で Gibbs 不等式を 1 行積分なしで処理。

## Phase A - 定義 ✅

- `entropyD D P := -Σ a, P.real {a} * Real.logb D (P.real {a})` (D-ary entropy)
- `shannonLength D P a : ℕ := ⌈-Real.logb D (P.real {a})⌉₊` (Shannon code 語長)
- `expectedLength P l := Σ a, P.real {a} * (l a : ℝ)` (期待長)
- `kraftSum D l := Σ a, (D : ℝ)^(-(l a : ℝ))` (Kraft 和) ※ ENNReal でなく Real (textbook 流儀)

## Phase B - Shannon 語長の Kraft 充足 ✅

- `shannonLength_kraft_le_one`: `D ≥ 2`, `P` proba ⟹ `kraftSum D (shannonLength D P) ≤ 1`
- 鍵: 各 `a` で `(D : ℝ)^(-shannonLength D P a) ≤ P.real {a}` ← `shannonLength ≥ -log_D P(a)` ← `Nat.le_ceil`
- 注意: `P.real {a} = 0` のケースは `shannonLength` が `0` で `D^0 = 1` になり破綻するため、後段の証明では `P.real {a} > 0` を場合分けで前提に取る (or `Set.support` で sum を制限)。

## Phase C - 期待長下界 (Gibbs) ✅

- `entropyD_le_expectedLength_of_kraft`: `D ≥ 2`, `P` proba, lengths `l : α → ℕ` が `kraftSum D l ≤ 1` ⟹ `entropyD D P ≤ expectedLength P l`
- 鍵: 各 `a` で `P.real {a} · (-logb D P(a) - l(a))` を `log_le_sub_one_of_pos` 経路で `(D^{-l(a)} - P.real {a}) / log D` で上界、Σ。Kraft 仮定で Σ `D^{-l(a)} ≤ 1`、proba で Σ `P.real {a} = 1`、よって差は ≤ 0。
- support 仮定: `P.real {a} = 0` の項は両側 0 で無問題 (`negMulLog 0 = 0` 同様、`0 · _ = 0`)。

## Phase D - 期待長上界 ✅

- `expectedLength_shannon_lt_entropyD_add_one`: `D ≥ 2`, `P` proba, `∀ a, P.real {a} > 0` ⟹ `expectedLength P (shannonLength D P) < entropyD D P + 1`
- 鍵: 各 `a` で `(shannonLength D P a : ℝ) < -logb D P(a) + 1` ← `Nat.ceil_lt_add_one`、`P.real {a} > 0` で乗じ、Σ。
- support 仮定: 厳密不等式のため `∀ a, P.real {a} > 0` (full support) が必要。これは仕様。

## Phase E - 主定理 ✅

- `shannonCode_expected_length_bounds`: 上記 3 つを束ねた sandwich
  `entropyD D P ≤ expectedLength P (shannonLength D P) ∧ expectedLength P (shannonLength D P) < entropyD D P + 1`

## 判断ログ

1. **Mathlib 側に prefix code 構造体は無い** (Phase 0 で確認、`InformationTheory/Coding/` 直下に `KraftMcMillan.lean` と `UniquelyDecodable.lean` のみ)。本シードは **語長水準** の formalization に絞ることで、文字列符号の構成を回避。Kraft 逆向き (prefix code 構成 from 充足) は B-8' に切り出す。
2. **`kraft_mcmillan_inequality` (Mathlib) は本シードで直接は使わない**: Mathlib の statement は uniquely decodable code (`Finset (List α)`) を入口に取るが、本シードは "Shannon 語長が Kraft を充足する" の **順向き** を独立に証明 (それで lower bound に十分)。Mathlib 形は将来 B-8' で逆向きを書くときに register。
3. **D-ary log 規約**: `Real.logb D` を採用 (`Mathlib.Analysis.SpecialFunctions.Log.Base`)。base-`e` の `Real.log` 形では `log D` factor が plumbing 全体に伝播するため、`logb` で書いて `log D` 因子を局所化。
4. **support 仮定の処理**: Phase C (下界) は full support 不要 (`P(a) = 0` 項は 0 で消える)。Phase D (上界、厳密不等式) は `∀ a, P(a) > 0` 仮定が本質的に必要 (`P(a) = 0` で `shannonLength` が `0`、`-logb 0 = 0` で等号化)。

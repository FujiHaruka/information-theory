# Loomis–Whitney 不等式 Lean 形式化 — ボトルネック分析

`Common2026/Shannon/HanDShearer.lean:41` の `shearer_inequality` を engine として、
情報理論ルートで textbook 形 Loomis–Whitney $|A|^{n-1} \le \prod_i |\pi_i(A)|$ を Lean 4 で
証明した記録。Common2026 で初めて **情報理論外 (純コンビ) の不等式** が sorry なしに
通った demo。本 proof-log は質的観察に絞る (定量データは `scripts/session_metrics.ts` 任せ)。

## 0. 対象問題と成果物

**最終定理** (`Common2026/Shannon/LoomisWhitney.lean`):

```lean
theorem loomis_whitney
    {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Finset (Fin n → α)} (hA : A.Nonempty) :
    A.card ^ (n - 1) ≤ ∏ i : Fin n, (projectionExcept i A).card
```

`projectionExcept i A := A.image (fun x j => x j.val)` は `i` 成分を抜いた射影像 (型は
`Finset ({j : Fin n // j ≠ i} → α)`)。

成果物:

- `Common2026/Shannon/LoomisWhitney.lean` — 444 行、0 errors / 0 sorry
  - `entropy_uniformOn_eq_log_card` (Phase A、~40 行)
  - `entropy_le_log_image_card` (Phase A、~80 行)
  - `projectionExcept` (def)
  - `jointEntropySubset_le_log_projectionExcept_card` (Phase B、~55 行)
  - `loomis_whitney` (主定理、Phase C、~85 行)
- `Common2026.lean` に `import Common2026.Shannon.LoomisWhitney` 追記
- `docs/shannon/loomis-whitney-moonshot-plan.md` ✅ + 判断ログ追記
- `docs/shannon/loomis-whitney-mathlib-inventory.md` (事前 inventory、本ターンでは更新なし)

`lake env lean Common2026/Shannon/LoomisWhitney.lean` silent / `lake build` 全体緑通過
(2752 jobs)。

## 1. 問題のキャラクター

「**engine (Shearer) 既製 + 確率論 ↔ 集合論翻訳 plumbing が支配項**」型。`shearer_inequality`
が既に `Common2026.Shannon.HanDShearer` で完走しているため、本ターンの Lean 作業は
2 つの **境界面** だけだった:

1. **入力境界**: `μ := uniformOn A`、`Xs i ω := ω i` を Shearer に渡せる形に整える
2. **出力境界**: Shearer から出る `(n-1) · H(Xs) ≤ ∑ i, H(X_{S_i})` の両辺を集合論的不等式
   `|A|^{n-1} ≤ ∏ i, |π_i(A)|` に翻訳する

(2) が支配項で、内訳は (a) `entropy_uniformOn_eq_log_card` (LHS 翻訳)、
(b) `entropy_le_log_image_card` + reshape (RHS 翻訳の per-summand)、
(c) log↔exp と Nat ↔ Real cast (主定理)。

## 2. 質的観察 (3 点)

### 観察 1: Mathlib に「support 圧縮 + uniform 化」型の補題は無いが、`negMulLog` 凹性 + `ConcaveOn.le_map_sum` で 1 段 Jensen が直接効いた

**事前計画では両論併記** (「support 圧縮 → uniform 化 → entropy_uniformOn_eq_log_card 経由」と
「`negMulLog` 凹性 (Jensen)」)、support 圧縮ルートは uniform への bijection plumbing が
重そうという理由で後回しにしていた。実機では **Mathlib `Real.concaveOn_negMulLog` +
`ConcaveOn.le_map_sum` が直接適用可能** で、`∑ y ∈ s, (1/|s|) • negMulLog (p y) ≤
negMulLog (∑ y ∈ s, (1/|s|) • p y)` で 1 段、両辺に `|s|` を掛けて
`∑ negMulLog p ≤ |s| · negMulLog (1/|s|) = log |s|` で着地。

**意義**: 「Mathlib 不在 = 自前で push 経路を書く」と早合点せず、関連する Mathlib API
(`ConcaveOn.le_map_sum` は Jensen の Finset 版) を grep / loogle で探すだけで 60 行が
30 行に縮む。本ターンで Phase A の `entropy_le_log_image_card` を 60 行で着地できたのは
ほぼこれのおかげ。インベントリの「自前 60〜80 行」見積は過大評価だった。

### 観察 2: `uniformOn_apply_finset` の戻り値は ENNReal、`Measure.real` 経由で `1/N` を取り出すのに `ENNReal.toReal_div` + `Nat.cast_one` の 2 step が要った

`uniformOn_apply_finset : uniformOn (s : Set Ω) (t : Set Ω) = #(s ∩ t) / #s` は ENNReal 値
だが、entropy の引数は `Measure.real` (= `ENNReal.toReal`) 経由で実数値。
`A ∩ {x} = {x}` (`x ∈ A` のとき) で `#(A ∩ {x}) = 1`、ENNReal の `1 / A.card` を
`ENNReal.toReal_div, ENNReal.toReal_one` で `1 / A.card : ℝ` に押し下げる箇所で
`Nat.cast_one` が前段に要った。インベントリには「1/N の取り出しは `uniformOn_apply_finset`
1 段」と書いていたが、実機ではその後の **`.toReal` 経由が +1 step** という 1 行の差。

`uniformOn_eq_zero_iff` (= `uniformOn s t = 0 ↔ s ∩ t = ∅`) は `entropy_le_log_image_card`
の support 外側 (`y ∉ A.image f` ⟹ `μ.map f {y} = 0`) で 1 行に効いた。インベントリでは
明示してなかった補題で、`Measure.map_apply` 後に `uniformOn (f ⁻¹' {y}) = 0` を
直接出すのに使った。**`cond_apply` を経由する遠回りを 5 行ぐらい省略できた**。

### 観察 3: 計画の「中間補題」と実機の「中間補題」のズレが 3 点

| 計画 (Phase A inventory) | 実機 |
|---|---|
| `entropy_image_le_log_card` (一般 β / γ、measurable f 引数) | `entropy_le_log_image_card` (同名同シグネチャ、Jensen ルートで 60 行) ─ 一致 |
| `marginal_entropy_le_log_image_card` (個別 i、Pi reshape を含む) | `jointEntropySubset_le_log_projectionExcept_card` (`Finset.univ.filter (· ≠ i)` 形に揃え、`piCongrLeft idx` で 1 段 reshape、~55 行) ─ 計画より名前を `Finset` 流儀に寄せた |
| **計画になかった**: `(univ.filter (· ≠ i)) ↔ {j // j ≠ i}` の index 同型 | 自前で `idx : ↥(univ.filter ...) ≃ {j // j ≠ i}` を 4 行で構築、`piCongrLeft` で Pi 値に押し上げ。**Han.lean の `exceptIdxEquiv` (private) は流用できず** (private 制約 + 形が `Fin i.val ⊕ {j // i < j}` で違う) |

3 つ目はインベントリの「**判断保留: `exceptIdxEquiv` の公開化**」で「再定義する (5 行で済む)」と
書いていたとおり、再定義 (4 行) で済んだ。Han Phase D の `exceptIdxEquiv` を public 化
する判断は不要だった。

## 3. Approach 段階で予測した plumbing と実機で必要だった plumbing のズレ

| 予測 (plan) | 実機 |
|---|---|
| `Real.exp` で持ち上げ (`Real.exp_le_exp` で `|A|^(n-1) ≤ ∏ \|π_i(A)\|`) | `Real.log_le_log_iff` の `.mp` 1 段で済んだ。`exp_log` 経由は不要、`log` の単調性逆向きで両辺正値性 (`pow_pos`、`Finset.prod_pos`) を渡すだけ |
| `Real.log_prod (s) (f) (hf)` (3 引数) | 実物は `{s} {f}` implicit + `(hf)` explicit の **1 引数**。インベントリ記述要訂正 (本 proof-log の判断ログに記録済み) |
| `Nat.cast_pow` / `Nat.cast_prod` で自然数版へ降ろす | `push_cast` 1 段 + `exact_mod_cast` で済んだ。手書き cast は不要 |

## 4. cover 条件の証明で `simp only` を **過剰に** かけてしまい rcases パターン破綻

`Finset.univ.filter (fun i => j ∈ S i) = Finset.univ.erase j` の `ext` 後、
最初は `simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, S,
Finset.mem_filter]` で全展開を試みたが、simp が `j ∈ S i ↔ i ≠ j ∧ True` 形まで畳んでしまい、
事前に書いていた `rintro ⟨_, hji⟩` が `j = i → False` (= `j ≠ i`) を inductive datatype として
分解しようとして失敗。

**修正**: 直接 `rw [Finset.mem_filter, Finset.mem_erase]` + 軽量 `simp only [Finset.mem_univ,
true_and, and_true, S, Finset.mem_filter]` に絞り、最後の `j ≠ i ↔ i ≠ j` を
`⟨fun h hij => h hij.symm, fun h hji => h hji.symm⟩` 1 行で締める形に変えたら通った。

**学び**: `simp only` の引数を盛り込みすぎると、後続の `rintro` / `rcases` がパターンを
失って、debug が「どこで simp が予期せず潰したか」の探索になる。simp は **最小集合** で
段階的にかけ、必要に応じて中間状態を `show` で明示する方針が safe。

## 5. 残課題 / フォローアップ

- **ヘテロ拡張** (`α : Fin n → Type` 各成分が違う型): 計画段階で「ヘテロ拡張は非ゴール」と
  明記してあり、本 plan では着手しない。Mathlib API (`MeasurableEquiv.piCongrLeft`,
  `MeasurableEquiv.piCongrRight`) は揃っているので、必要になれば 30 行追加で済む見込み。
- **応用例**: Brunn–Minkowski / discrete isoperimetric の Loomis–Whitney 経由証明を
  Common2026 で展開する余地あり。Seed カードに記録しておくべき (= 次のムーンショット候補)。

## 6. 振り返り (4 行)

1. Mathlib `ConcaveOn.le_map_sum` 直接適用が想定より早く効き、Phase A 後半が 30 行短縮。
2. `uniformOn_eq_zero_iff` (= `uniformOn s t = 0 ↔ s ∩ t = ∅`) は support 外側証明の最短路。
3. cover 条件は simp の盛り込み過多で 1 ターン溶かした。simp は最小集合で段階適用が default。
4. インベントリの `Real.log_prod` 引数記述ミスは proof-log で訂正、次回更新時に inventory も修正。

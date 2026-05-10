# Loomis–Whitney ムーンショット計画 🌙

> **Status (2026-05-10): 起草。** Han Phase D 完了 (`Common2026/Shannon/HanD*.lean` の 8
> 主定理が 0 sorry) と `Common2026/Shannon/Pi.lean` 切り出し直後の最初のムーンショット。
> Seed カード ([`docs/moonshot-seeds.md` Seed 1](../moonshot-seeds.md)) を母体に Phase 分解した。
>
> ゴールは textbook 形 Loomis–Whitney 不等式 $|A|^{n-1} \le \prod_{i} |\pi_i(A)|$ を、Han
> Phase D の `shearer_inequality` を engine として情報理論的に証明すること。**情報理論外**
> (純コンビ) の不等式が Lean で sorry なしに通る初の Common2026 demo になる。

## 進捗

- [x] Phase 0 — Mathlib + 既存 Common2026 API インベントリ ✅ → [`loomis-whitney-mathlib-inventory.md`](loomis-whitney-mathlib-inventory.md)
- [x] Phase A — counting measure 上の entropy plumbing (`entropy_uniformOn_eq_log_card` / `entropy_le_log_image_card`) ✅
- [x] Phase B — 射影 plumbing (`jointEntropySubset_le_log_projectionExcept_card`, `Pi.lean` の `entropy_measurableEquiv_comp` で reshape) ✅
- [x] Phase C — Shearer 適用 + 射影像濃度との接続 (`loomis_whitney` 主定理) ✅

**完了 (2026-05-10)**: `Common2026/Shannon/LoomisWhitney.lean` (444 行) が sorry ゼロで
`lake env lean` silent 通過 + `lake build` 全体緑通過。
proof-log: [`docs/proof-logs/proof-log-loomis-whitney.md`](../proof-logs/proof-log-loomis-whitney.md)

## ゴール / Approach

**ゴール**: 任意 $n \ge 1$ の有限族 `α : Fin n → Type` 上の有限部分集合 `A : Finset (Π i, α i)` に対し
$$
|A|^{n-1} \le \prod_{i : \text{Fin}\,n} |\pi_i(A)|, \qquad \pi_i(A) := \{x \restriction \{j \ne i\} \mid x \in A\}
$$
を証明する。本計画ではホモジニアス版 (`α i = α` 固定) で着地し、ヘテロ拡張は非ゴール。

**Approach (戦略の shape)**:

1. `μ := uniformOn (A : Set (Fin n → α))` を取り、確率変数 `Xs i ω := ω i` を考える。
2. **`entropy μ Xs = log |A|` の橋渡し補題** を 1 本書く (Phase A)。これは uniform on a finset の entropy が cardinality の log になる古典等式。Mathlib に直接の補題は無い (要 inventory) ので自前で書く。`uniformOn_apply_finset` (Mathlib) + `Real.negMulLog` の代数で 30〜50 行。
3. `S i := {j : Fin n | j ≠ i} : Finset (Fin n)` (各 `j` は `n−1` 個の `S i` に被覆される) を `shearer_inequality` に渡す。Shearer は `(n − 1) · jointEntropy μ Xs ≤ ∑ i, jointEntropySubset μ Xs (S i)` を返す。
4. **各 marginal 項 `jointEntropySubset μ Xs (S i) ≤ log |π_i(A)|`** を示す (Phase B-C)。これは `(j : ↥S i) → α` 値 RV の像が `π_i(A)` に含まれる + uniform-on-image の entropy ≤ uniform-on-superset の entropy という 2 段。前段は `Finset.image` の濃度引数、後段は Phase A の橋渡し補題の押し出し版。
5. 両辺を整理して `(n − 1) · log |A| ≤ ∑ i, log |π_i(A)| = log (∏ i, |π_i(A)|)` を取り、`Real.exp` で持ち上げて主定理 ($|A|^{n-1} \le \prod_i |π_i(A)|$) を得る (Phase C)。

ファイル構成 (Phase C 終了時):

```
Common2026/Shannon/
  HanDShearer.lean   ← 既存 (engine: shearer_inequality)
  Pi.lean            ← 既存 (entropy/condEntropy MeasurableEquiv 不変性)
  LoomisWhitney.lean ← 新規: entropy_uniformOn_eq_log_card,
                        marginal_entropy_le_log_image_card,
                        loomis_whitney
```

`Common2026.lean` (library root) に `import Common2026.Shannon.LoomisWhitney` を追記。

## Phase 0 — Mathlib + 既存 Common2026 API インベントリ 📋

サブ計画: [`loomis-whitney-mathlib-inventory.md`](loomis-whitney-mathlib-inventory.md)

- [ ] **軸 1: Loomis–Whitney 自体** — Mathlib に `loomis_whitney` 系の不等式が既存していないか確認。textbook 名 / 統計力学的命名 / `card_le_prod_card_image` 系
- [ ] **軸 2: counting measure / uniformOn**: `MeasureTheory.Measure.count`, `ProbabilityTheory.uniformOn` の API 在庫。確率測度化条件 + `uniformOn_apply_finset` で singleton 質量 `1 / |A|` を取り出せるか
- [ ] **軸 3: 一様分布 entropy ↔ 濃度** — `entropy μ Xs = log |A|` の橋渡し補題。`Real.log_pow` / `Real.negMulLog (1/N) = (log N) / N` の代数支援補題
- [ ] **軸 4: 射影 (drop-one-coordinate)** — `Common2026.Shannon.Han.exceptIdxEquiv` / `MeasurableEquiv.piFinSuccAbove` / `Common2026.Shannon.Pi.entropy_measurableEquiv_comp` の流用可能性
- [ ] **軸 5: `shearer_inequality`** — 本 plan 適用形 (`S i := {j ≠ i} : Finset (Fin n)`) のシグネチャと cover 条件 `∀ i, k ≤ #(univ.filter (fun j => i ∈ S j))` の評価。`k = n − 1` で通るか

各軸で「Mathlib にあるか / ないか / 既存補題で代用可」を 1 行結論で記録。`Done` 条件は **「Phase A skeleton (`Common2026/Shannon/LoomisWhitney.lean` の sorry-driven 出だし) が書ける状態」**。

## Phase A — counting measure 上の entropy plumbing 📋

ターゲット: `μ := uniformOn (A : Set _)` のもとで `entropy μ (fun ω i => ω i) = Real.log #A` を示す橋渡し補題群。

### スコープ (skeleton)

```lean
namespace InformationTheory.Shannon.LoomisWhitney

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- 一様分布 entropy: `μ = uniformOn (A : Set β)` のもとで `entropy μ id = log #A`。 -/
theorem entropy_uniformOn_eq_log_card
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    {A : Finset β} (hA : A.Nonempty) :
    entropy (uniformOn (A : Set β)) (id : β → β) = Real.log A.card

/-- 像での entropy ≤ 全体 entropy。`f : β → γ` で `μ.map f` は image set に集中する。 -/
theorem entropy_image_le_log_card
    {β γ : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {A : Finset β} (hA : A.Nonempty)
    (f : β → γ) (hf : Measurable f) :
    entropy (uniformOn (A : Set β)) f ≤ Real.log (A.image f).card

end InformationTheory.Shannon.LoomisWhitney
```

### 鍵となる作業

- [ ] `entropy_uniformOn_eq_log_card`:
  - `μ.map id = uniformOn A` (定義展開)
  - 各 `x ∈ A` で `(uniformOn A).real {x} = 1 / #A` (`uniformOn_apply_finset` から導く)
  - `Real.negMulLog (1/N) = (log N) / N` を代数で出す (`Real.log_inv` / `Real.log_pow` 系)
  - `entropy = ∑ x ∈ A, negMulLog (1/N) + ∑ x ∉ A, negMulLog 0 = N · (log N / N) = log N`
  - 50 行見積。`hA : A.Nonempty` は `IsProbabilityMeasure (uniformOn A)` を出すために必須
- [ ] `entropy_image_le_log_card`:
  - `entropy μ f ≤ log #(image f univ)` の一般版 = "support の濃度の log を超えない"
  - 戦略: `(μ.map f).support ⊆ A.image f`、support 上の uniform 化 + `negMulLog` の凹性 (Jensen)、もしくは support に持って行ったあと Phase A 主補題で押し切る
  - **Mathlib に generic な "entropy ≤ log #support" は無い見込み (要 Phase 0 確認)**。あれば直接使う、無ければ `negMulLog` 凹性で 60〜80 行
- [ ] `Common2026.lean` に `import Common2026.Shannon.LoomisWhitney` を追記
- [ ] `lake env lean Common2026/Shannon/LoomisWhitney.lean` で silent 化

### Done 条件

- 上記 2 主定理が 0 sorry
- Phase B 着手判定 (`(j : ↥S i) → α` 値 RV への押し出しが `Pi.lean` の `entropy_measurableEquiv_comp` で済むことを確認)

### 工数感

3〜5 日 (`entropy_uniformOn_eq_log_card` + `entropy_image_le_log_card` で 80〜130 行)。

## Phase B — 射影 plumbing 📋

ターゲット: `Xs : Fin n → ((j : Fin n) → α) → α` (= 第 i 成分取り出し) に対し、subset `S i := {j ≠ i} : Finset (Fin n)` 上の `jointEntropySubset μ Xs (S i)` を「`A` を `i` 成分で射影した像 `π_i(A) : Finset ({j // j ≠ i} → α)` の log 濃度」と接続する。

### スコープ

```lean
/-- `i` を除いた成分の射影 (Finset 値)。 -/
def projectionExcept (i : Fin n) (A : Finset (Fin n → α)) :
    Finset ({j : Fin n // j ≠ i} → α) :=
  A.image (fun x j => x j.val)

/-- 射影 entropy ≤ 射影像濃度の log。Phase A の `entropy_image_le_log_card`
+ `Xs : (Fin n → α) → α` の `MeasurableEquiv` (`{j ≠ i} → α` 像の取り出し) を合成。 -/
theorem jointEntropySubset_le_log_projection_card
    {A : Finset (Fin n → α)} (hA : A.Nonempty) (i : Fin n) :
    let μ := uniformOn (A : Set (Fin n → α))
    let Xs : Fin n → (Fin n → α) → α := fun i ω => ω i
    jointEntropySubset μ Xs ({j : Fin n | j ≠ i}.toFinset)
      ≤ Real.log (projectionExcept i A).card
```

### 鍵となる作業

- [ ] **`{j : Fin n | j ≠ i}.toFinset` と `Finset.univ.filter (· ≠ i)` の同値 reshape**: `S i` を Phase D 系 plumbing が期待する形に揃える (Phase 0 で形を揃えるか判断、おそらく後者)
- [ ] **`fun ω (j : ↥(S i)) => ω j.val` を Phase A の `entropy_image_le_log_card` に乗せる**: `f : (Fin n → α) → ({j // j ∈ S i} → α)` の image が `projectionExcept i A` に一致することを `Finset.image_image` で示す
- [ ] **measurability**: `f` の measurability は `measurable_pi_iff` + 各成分 `Measurable.eval`
- [ ] `jointEntropySubset_le_log_projection_card` を Phase A 経由で証明 (`entropy_image_le_log_card` を一段適用する形、20〜40 行見込み)

### Done 条件

- 上記主定理が 0 sorry
- Phase C で `shearer_inequality` 適用後の RHS 各項が `log |π_i(A)|` に一致することが確認可能

### 工数感

2〜3 日 (Phase A の補題が揃っていれば adapter 1 本で済む見込み)。

## Phase C — Shearer 適用 + 主定理 📋

ターゲット: Loomis–Whitney 不等式本体。Shearer engine + Phase A/B の橋渡しで結論。

### スコープ

```lean
/-- Loomis–Whitney 不等式 (整数ホモジニアス版)。 -/
theorem loomis_whitney
    {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Finset (Fin n → α)} (hA : A.Nonempty) :
    A.card ^ (n - 1) ≤ ∏ i : Fin n, (projectionExcept i A).card
```

### 証明骨格

```
H(X_{[n]}) = log |A|                                     -- Phase A entropy_uniformOn_eq_log_card
(n - 1) * H(X_{[n]}) ≤ ∑ i, H(X_{S i})                   -- shearer_inequality with k = n - 1
                                                            (cover 条件: 各 j は n - 1 個の S i に出現)
H(X_{S i}) ≤ log |π_i(A)|                                -- Phase B jointEntropySubset_le_log_projection_card
∴ (n - 1) * log |A| ≤ ∑ i, log |π_i(A)| = log (∏ i, |π_i(A)|)
log の単調性 (Real.exp_log を経由) で
|A|^(n-1) ≤ ∏ i, |π_i(A)|
```

### 鍵となる作業

- [ ] **cover 条件の証明**: `∀ j : Fin n, n − 1 ≤ #(univ.filter (fun i => j ∈ S i))`。`S i = {j' | j' ≠ i}` なので `j ∈ S i ↔ j ≠ i`、よって `univ.filter (fun i => j ∈ S i) = univ.erase j`、その card は `n − 1`。等号で十分なので `le_of_eq` で `≤` 化
- [ ] **`shearer_inequality` 呼び出し**: 上の cover で `(↑(n − 1) : ℝ) * jointEntropy μ Xs ≤ ∑ i, jointEntropySubset μ Xs (S i)` を取得
- [ ] **LHS = `(n − 1) · log |A|`**: Phase A `entropy_uniformOn_eq_log_card` + `jointEntropy = entropy μ (fun ω i => ω i)` (`jointEntropy` 定義展開)
- [ ] **RHS ≤ `∑ i, log |π_i(A)|`**: Phase B 主定理を `Finset.sum_le_sum` で各項に適用
- [ ] **`∑ log = log ∏`**: `Real.log_prod` (要 Mathlib 確認、各項の正値性は `hA.image` 経由で `(projectionExcept i A).card > 0`)
- [ ] **`Real.exp` で持ち上げ**: `Real.log_le_log` の逆 = `Real.exp_le_exp` で `|A|^(n−1) ≤ ∏ |π_i(A)|`
  - `Real.exp_log` の正値前提を確保するため `hA` から `A.card > 0`、`(projectionExcept i A).card > 0` を引き出す
  - 自然数版に戻すには `Nat.cast_le` + `pow_le_pow` 系の代数。Mathlib に `Nat.cast_pow` / `Nat.cast_prod` あり

### Done 条件

- `loomis_whitney` が `lake env lean Common2026/Shannon/LoomisWhitney.lean` で silent
- `Common2026.lean` の import 確定

### 工数感

3〜5 日 (cover 条件 + log↔exp 持ち上げ + cast 代数。`Real.log_prod` 等の API が Phase 0 で揃っていれば 100〜150 行)。

## 失敗判定 / 撤退ライン

- **Phase 0 で Mathlib に Loomis–Whitney 既存** → 計画破棄、proof-log だけ取って Seed 2 (Polymatroid) に乗り換え
- **Phase A の `entropy_uniformOn_eq_log_card` で 1 週間以上溶ける** (uniformOn の API 不足等) → counting measure を使わず `Multiset.PMF.uniformOfFinset` 等の PMF 形に逃げる、もしくは Bridge 経由で Fano の PMF 形 `Fano/Entropy.lean` に対応版を書いて Loomis–Whitney も PMF 形に降ろす
- **Phase B の `entropy_image_le_log_card` 一般版で詰まる** → `Xs (S i)` の image が projection に一致することを *直接* 示す形 (一般化を諦めて Loomis–Whitney 専用補題で済ます)
- **Phase C の cast / `Real.exp` 持ち上げで詰まる** → 主定理を `Real` 版 (`(A.card : ℝ)^(n−1) ≤ ∏ ...`) で publish、自然数版は別補題で

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-10 実装ターン

- **Phase A `entropy_le_log_image_card` のルート確定**: 計画では「support 圧縮 → uniform 化 → Phase A 主補題」と「`negMulLog` 凹性 (Jensen)」の両論併記だったが、
  実機では Mathlib `Real.concaveOn_negMulLog` + `ConcaveOn.le_map_sum` が直接使えたので Jensen ルート 1 本で 60 行に収まった。
  uniform 化の bijection 経路は採用せず。
- **`uniformOn` の confidence 値の取り出し**: `uniformOn_apply_finset` は ENNReal 戻り値で
  `Measure.real` (= `.toReal`) との橋渡しで `ENNReal.toReal_div` + `Nat.cast_one` で 1 step、
  `Finset.inter_singleton_of_mem` / `_of_notMem` で場合分け。`uniformOn_eq_zero_iff` は
  support 外側の証明で 1 行に効いた (計画では明示してなかった補題)。
- **cover 条件の `ext` 後の simp**: `j ∈ S i ↔ i ≠ j` の双方向化で、最初 `simp only [...]`
  で過剰に潰してしまい rcases パターンが通らなかった。直接 `Finset.mem_filter` /
  `Finset.mem_erase` で展開し `⟨fun h hij => h hij.symm, ...⟩` で 1 行化が結果的に最短。
- **`Real.log_prod` の引数順序**: 既存インベントリの記述では `_ _ (fun i _ => ...)` と
  3 引数で書いていたが、実物は `{s} {f}` implicit + `(hf)` explicit の 1 引数で
  `Real.log_prod (fun i _ => h_proj_ne i)` 1 段で済む。インベントリ要訂正。

# AEP Phase D — 源符号化定理 weak converse ムーンショット計画 🌙

<!--
雛形メモ:
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
- `rg "^- \[ \]"` で残タスク横断 grep、`rg "🔄"` でピボット箇所だけ拾える
-->

> **Status (2026-05-11)**: 起草。AEP moonshot ([`aep-moonshot-plan.md`](aep-moonshot-plan.md))
> の Phase D を分離して deferred 単独 plan 化。
> シードカード ([`moonshot-seeds.md` "次のシード候補 A. 直接 deferred"](../moonshot-seeds.md#a-直接-deferred)) の見積
> 300〜500 行 / 中リスク / 1〜1.5 週間 を起点に膨らませた。
>
> **撤退ライン**: Phase A (`H(X^n) = n · H(X)` for i.i.d.) 緑通過時点で **「i.i.d. block entropy の Pi 化 chain rule」** という汎用補題が立つ。Phase B/C で詰まる場合は撤退ライン到達済とし、次セッションへ Phase D 主定理を再分離。

## 進捗

- [x] Phase 0 — Mathlib + 既存 Common2026 API インベントリ ✅ → [`aep-source-coding-mathlib-inventory.md`](aep-source-coding-mathlib-inventory.md)
- [ ] Phase A — i.i.d. block entropy chain rule (`H(X^n) = n · H(X)` + 補助 2 本) 📋
- [ ] Phase B — per-n converse bound (`H(X^n) ≤ log M_n + h(Pe_n) + Pe_n · n · log |α|`、Slepian–Wolf 流儀の 4-step 骨格再演) 📋
- [ ] Phase C — `Filter.liminf` 形主定理 (`entropy μ (Xs 0) ≤ liminf (log M_n / n) atTop`) 📋
- [ ] Phase D — verify (`lake env lean Common2026/Shannon/AEP.lean` silent + proof-log + metrics) 📋

## ゴール / Approach

**最終到達点**: 源符号化定理 weak converse —
任意のブロック符号 `c_n / d_n` で `P{d_n(c_n(X^n)) ≠ X^n} → 0` ⟹ `liminf_n (log M_n / n) ≥ entropy μ (Xs 0)`。

**Approach の中核 (3 段)**:

1. **(a) i.i.d. block entropy の Pi 化 chain rule (Phase A)** ─ `H(X^n) = n · H(X)` を `iIndepFun` 仮定下で確立。Han `jointEntropy_chain_rule` (n-variable form `H = ∑ H(X_i | prefix)`) を base に、各 summand を `condEntropy_eq_entropy_of_indepFun` (新規補題 1) と `entropy_eq_of_identDistrib` (新規補題 2) で `H(X_0)` に潰す。**Pairwise IndepFun では不十分** (Bernstein counterexample)、Phase D の statement は `iIndepFun` を新規追加仮定として受ける (inventory 軸 2 の結論)
2. **(b) per-n の converse bound (Phase B)** ─ Slepian–Wolf converse の 4-step 流儀を `(Msg := X^n, Yo := c n ∘ X^n, decoder := d n)` で再演:
   - **Step A**: `H(c n ∘ X^n) ≤ log (M n)` (`entropy_le_log_card`、SlepianWolf.lean)
   - **Step B**: `I(X^n; c n ∘ X^n) ≤ H(c n ∘ X^n)` (mutualInfo bridge + condEntropy ≥ 0)
   - **Step C**: `H(X^n | c n ∘ X^n) ≤ H(X^n | d n ∘ c n ∘ X^n)` (DPI の conditioner 側 = `mutualInfo_le_of_postprocess`)
   - **Step D**: `H(X^n | d n ∘ c n ∘ X^n) ≤ h(Pe_n) + Pe_n · log(|α|^n - 1)` (`fano_inequality_measure_theoretic`、`X := Fin n → α` で適用)
   - **組成**: `H(X^n) = I(X^n; c n ∘ X^n) + H(X^n | c n ∘ X^n) ≤ log(M n) + h(Pe_n) + Pe_n · n · log |α|` (`log(|α|^n - 1) ≤ n · log |α|` で簡略化)
3. **(c) `Filter.liminf` 形 (Phase C)** ─ Phase A の `H(X^n) = n · H(X)` と Phase B の per-n bound を連結し `n · H(X) ≤ log M_n + δ_n` で `δ_n := h(Pe_n) + Pe_n · n · log |α|`。両辺 `/n` で `H(X) ≤ log M_n / n + δ_n / n`。`δ_n / n → 0` を `Pe_n → 0` (仮定) + `1/n → 0` から組成、`Tendsto (H − δ_n / n) atTop (𝓝 H)` で `liminf_le_liminf` + `Tendsto.liminf_eq` (Mathlib `Filter.liminf` API、inventory 軸 1 で完備確認済)

**Approach 図**:

```
Phase 0  : Mathlib + Common2026 API インベントリ              ← 完 (本 plan + inventory 起草)
           ──────────────────────────────────────────
Phase A  : i.i.d. block entropy chain rule (H(X^n) = n · H(X))  ← 山場 1、80〜150 行、3〜5 日
           ──────────────────────────────────────────
Phase B  : per-n converse bound (Slepian–Wolf 流儀 4-step)      ← 中盤、80〜120 行、3〜5 日
           ──────────────────────────────────────────
Phase C  : Filter.liminf 形主定理 + Phase A/B 統合              ← 終段 plumbing、50〜80 行、2〜3 日
           ──────────────────────────────────────────
Phase D  : lake env lean silent + proof-log + metrics           ← verify、半日
```

**ファイル構成**:

```
Common2026/Shannon/
  AEP.lean             ← Phase A〜C 既存 (432 行)
                       ← 本 plan は **末尾 append** (Phase A〜C in source-coding 部分)、
                          ファイル分割は line 数が 800〜1000 を超えたら検討
```

または:

```
Common2026/Shannon/
  AEP.lean             ← Phase A〜C 既存 (432 行)
  SourceCoding.lean    ← 本 plan の Phase A〜C (新ファイル)
```

**判断**: 既存 AEP の `jointRV` / `pmfLog` plumbing を直接使う + Phase A の `condEntropy_eq_entropy_of_indepFun` / `entropy_eq_of_identDistrib` は AEP 以外でも汎用なので **新ファイル `SourceCoding.lean` を作って `import AEP` で受ける**方が clean。最終判断は Phase A 着手時点で AEP.lean の line 数を見て決める。

---

## Phase 0 — Mathlib + 既存 Common2026 API インベントリ ✅

### スコープ

[`aep-source-coding-mathlib-inventory.md`](aep-source-coding-mathlib-inventory.md) を起草、5 軸 (`Filter.liminf` API / i.i.d. 強化 (`iIndepFun`) / Pi 化 entropy chain rule / ソース符号化 formalism / 既存資産 4 部品) を裏取り。

### 結論

- **Filter.liminf API** は Mathlib 完備 (`Filter.Tendsto.liminf_eq` / `liminf_le_liminf`)、自前補題不要
- **`Pairwise IndepFun → iIndepFun` 変換は不可** (Bernstein counterexample)、Phase D は `iIndepFun` 仮定を新規追加
- **Pi 化 entropy chain rule (`H(X^n) = n · H(X)`) は Common2026 / Mathlib 共に不在**、自前 80〜150 行
- **ソース符号化 formalism は Mathlib 不在**、既存 `MeasureFano.errorProb` を直接利用 (`SourceCode` 構造体は不要)
- **`shannon_converse_single_shot` は uniform 仮定により直接呼び不可**、骨格再演に必要な 4 部品 (`entropy_le_log_card` / `mutualInfo_eq_entropy_sub_condEntropy` / `mutualInfo_le_of_postprocess` / `fano_inequality_measure_theoretic`) はすべて既存

### Done 条件 (Phase 0)

- [x] 5 軸調査完了 (inventory)
- [x] Phase A skeleton (`condEntropy_eq_entropy_of_indepFun` / `entropy_eq_of_identDistrib` / `entropy_jointRV_eq_n_smul`) が書ける状態
- [x] Phase B skeleton (Slepian–Wolf 流儀 4-step 再演) が書ける状態
- [x] Phase C skeleton (Filter.liminf 形 + Phase A/B 統合) が書ける状態

### 工数感

1 ターン (本 plan 起草 = 完)。

---

## Phase A — i.i.d. block entropy chain rule (`H(X^n) = n · H(X)`) 📋

### スコープ

```lean
namespace InformationTheory.Shannon

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                    [MeasurableSpace α] [MeasurableSingletonClass α]

/-- 補助 1: 独立条件付き ⇒ condEntropy = entropy. -/
lemma condEntropy_eq_entropy_of_indepFun
    {β : Type*} [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y)
    (hindep : X ⟂ᵢ[μ] Y) :
    InformationTheory.MeasureFano.condEntropy μ X Y = entropy μ X

/-- 補助 2: identDistrib ⇒ entropy 等. -/
lemma entropy_eq_of_identDistrib
    (μ ν : Measure Ω) (X Y : Ω → α)
    (h : IdentDistrib X Y μ ν) :
    entropy μ X = entropy ν Y

/-- **Pi 化 entropy chain rule for i.i.d. blocks**: `H(X^n) = n · H(X_0)`. -/
theorem entropy_jointRV_eq_n_smul
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (n : ℕ) :
    entropy μ (jointRV Xs n) = (n : ℝ) * entropy μ (Xs 0)

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(A.1) `condEntropy_eq_entropy_of_indepFun`** ─ 戦略: `mutualInfo_eq_entropy_sub_condEntropy μ X Y hX hY` で `(mutualInfo μ X Y).toReal = entropy μ X − condEntropy μ X Y`、`mutualInfo_eq_zero_iff_indep` (`Common2026/Shannon/MutualInfo.lean:109`、両方向の片向き) で `mutualInfo μ X Y = 0` ⟹ `entropy μ X − condEntropy μ X Y = 0`。**注意**: `mutualInfo_eq_zero_iff_indep` の正確な statement が双方向か片方向かを確認。`X ⟂ᵢ[μ] Y → mutualInfo μ X Y = 0` 方向が必要。30〜50 行
- [ ] **(A.2) `entropy_eq_of_identDistrib`** ─ 戦略: `entropy` の定義 `∑ x : α, Real.negMulLog ((μ.map X).real {x})`、`IdentDistrib.map_eq : μ.map X = ν.map Y`、点ごと書き換え。10〜20 行。**注意**: `IdentDistrib` の `map_eq` field は `AEMeasurable` 仮定下でも成立、entropy の定義は `(μ.map X).real {x}` という measure-real 値のみ使うので `Measurable` vs `AEMeasurable` 区別不要
- [ ] **(A.3) `entropy_jointRV_eq_n_smul` の zero case (`n = 0`)** ─ `jointRV Xs 0 : Ω → (Fin 0 → α)`、codomain は `Unique` (Pi.uniqueOfIsEmpty)、entropy = `negMulLog 1 = 0`、RHS = `0 · H = 0`。Han Phase B `jointEntropy_chain_rule` の base case と同形 (5〜15 行)
- [ ] **(A.4) `entropy_jointRV_eq_n_smul` の successor case (`n + 1`)** ─ 戦略 (主路線):
  - Step 1: `jointRV Xs (n+1) ω` を `(Xs n ω, jointRV Xs n ω)` の pair として書き換える MeasurableEquiv (Han の `MeasurableEquiv.piFinSuccAbove (Fin.last n)` と同じ)。**重要**: `entropy_measurableEquiv_comp` (`Pi.lean:45`) で `entropy μ (jointRV Xs (n+1)) = entropy μ (fun ω => (Xs n ω, jointRV Xs n ω))`
  - Step 2: `entropy_pair_eq_entropy_add_condEntropy` (`Entropy.lean:41`) で `entropy μ (Xs n, jointRV Xs n) = entropy μ (jointRV Xs n) + condEntropy μ (Xs n) (jointRV Xs n)` (注: pair の順序、order is `(Xs n, prefix)` → `H(Xs n) + H(prefix | Xs n)` か `H(prefix) + H(Xs n | prefix)` か要 case 分け、Han `jointEntropy_chain_rule` の successor case を参照)
  - Step 3: `condEntropy μ (Xs n) (jointRV Xs n) = entropy μ (Xs n)` ─ A.1 を `Xs n ⟂ᵢ jointRV Xs n` から導出。**`iIndepFun.indepFun_finset` (`Mathlib/Probability/Independence/Basic.lean:839`)** を `S = {n}`, `T = Finset.range n` で適用 (Disjoint は `Finset.disjoint_singleton_right` + `Finset.notMem_range_self`)、結論を `IndepFun (Xs n) (fun ω j => Xs (j.val) ω)` の形に整形 (Pi 値 reshape の `MeasurableEquiv` で 1 段)。**ここの reshape が Phase A の最大不確実性**
  - Step 4: `entropy μ (Xs n) = entropy μ (Xs 0)` ─ A.2 を `hident n` に適用
  - Step 5: `entropy μ (jointRV Xs n) = n · entropy μ (Xs 0)` ─ IH
  - 組成: `(n+1) · entropy μ (Xs 0) = n · entropy μ (Xs 0) + entropy μ (Xs 0) = entropy μ (jointRV Xs n) + entropy μ (Xs 0)` ✓
  - 60〜100 行 (主路線)、または **代替**: A.3/A.4 を 2 つに分けず `Han.jointEntropy_chain_rule` を直接呼んで induction 不要のラインで書ける可能性 (要 Phase A 着手時の判断、jointEntropy_chain_rule の summand `condEntropy μ (Xs i) prefix_i` を A.1 + A.2 で各 i ごとに `entropy μ (Xs 0)` に潰し、`Finset.sum_const` で `n · H(X_0)` を出す。20〜40 行で済む可能性あり)

### Done 条件

- [ ] 上記 4 項目が `lake env lean Common2026/Shannon/AEP.lean` (or 新ファイル) で silent
- [ ] skeleton-driven で A.1 → A.2 → A.3 → A.4 の sorry を割る順序

### 工数感

3〜5 日 (80〜150 行)。**最大リスク**: A.4 Step 3 の Pi 値 reshape (`Xs n ⟂ᵢ jointRV Xs n` の Pi 値 conditioner 側を `iIndepFun.indepFun_finset` の `(j : Finset.range n) → Ω → α` 形と整合)。Han Phase B successor case で類似の reshape (`MeasurableEquiv.piFinSuccAbove`) は通っているので前例あり。

### 撤退ライン (Phase A 内)

- A.4 Step 3 の reshape で 3〜5 日溶ける場合 → **代替路線**: `Han.jointEntropy_chain_rule` を直接呼んで n 変数 chain rule の summand を各 i ごとに潰す (induction 不要)。後者で plumbing が薄くなる可能性が高い
- A.1 で `mutualInfo_eq_zero_iff_indep` が片向きしか提供されていない場合 → 自前で逆向きを書き下ろす (mutualInfo の積分形 unfold + Jensen 等号条件、20〜30 行)

---

## Phase B — per-n converse bound (Slepian–Wolf 流儀 4-step) 📋

### スコープ

```lean
namespace InformationTheory.Shannon

/-- per-n converse bound: `n · H(X) ≤ log M_n + h(Pe_n) + Pe_n · n · log |α|`. -/
theorem source_coding_per_n_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α)
    (n : ℕ) (hn : 1 ≤ n)
    (M : ℕ) (hM_pos : 0 < M)
    (c : (Fin n → α) → Fin M)
    (d : Fin M → (Fin n → α)) :
    (n : ℝ) * entropy μ (Xs 0)
      ≤ Real.log (M : ℝ)
        + Real.binEntropy
            (InformationTheory.MeasureFano.errorProb μ
              (jointRV Xs n) (fun ω => c (jointRV Xs n ω)) d)
        + InformationTheory.MeasureFano.errorProb μ
            (jointRV Xs n) (fun ω => c (jointRV Xs n ω)) d
          * (n : ℝ) * Real.log (Fintype.card α)

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(B.0) Setup**: `set X^n := jointRV Xs n`, `set Yo_n := c ∘ X^n`, `set Pe_n := errorProb μ X^n Yo_n d`. 各 measurability:
  - `hX^n : Measurable X^n` ─ `measurable_jointRV` (既存、AEP.lean:53)
  - `hYo_n : Measurable Yo_n` ─ `c` は `measurable_of_countable _` (Fin (M n) は Fintype)、`hYo_n = (measurable_of_countable c).comp hX^n`
  - `hd : Measurable d` ─ 同上 `measurable_of_countable d`
  - `hcard_Mn : (Fintype.card (Fin M) : ℝ) = M` ─ `Fintype.card_fin`
  - `hcard_Pi : 2 ≤ Fintype.card (Fin n → α)` ─ `Fintype.card_fun` + `Fintype.card_fin n` で `(Fintype.card α)^n ≥ 2^1 = 2` (`hn : 1 ≤ n` + `hcard : 2 ≤ Fintype.card α`)、5〜10 行
- [ ] **(B.1) Step A**: `entropy μ Yo_n ≤ Real.log M` ─ `entropy_le_log_card μ Yo_n hYo_n` を直接適用、`hcard_Mn` で書き換え。3〜5 行
- [ ] **(B.2) Step B**: `(mutualInfo μ X^n Yo_n).toReal ≤ entropy μ Yo_n` ─ `mutualInfo_eq_entropy_sub_condEntropy` (Bridge.lean:579 の対称形) または `mutualInfo_comm` + bridge で `(mutualInfo μ X^n Yo_n).toReal = entropy μ Yo_n − condEntropy μ Yo_n X^n`、`condEntropy ≥ 0` (`condEntropy_nonneg` Pi.lean:108) で結論。10〜15 行
- [ ] **(B.3) Step C**: `condEntropy μ X^n Yo_n ≤ condEntropy μ X^n (d ∘ Yo_n)` ─ DPI 系 (条件側の deterministic post-process は条件付きエントロピーを **増やさない**、wait — 実際は減らさない ⟹ 不等号の向きが逆)。実際の使い方は **`H(X^n | Yo_n) ≤ H(X^n | d ∘ Yo_n)`** ではなく **`H(X^n) − H(X^n | d ∘ Yo_n) ≤ H(X^n) − H(X^n | Yo_n)`** で `I(X^n; d ∘ Yo_n) ≤ I(X^n; Yo_n)`。`mutualInfo_le_of_postprocess` (DPI.lean:139) を `(Y, decoder) := (Yo_n, d)` で適用。10〜15 行
- [ ] **(B.4) Step D**: `condEntropy μ X^n (d ∘ Yo_n) ≤ h(Pe_n) + Pe_n · log(|α|^n - 1)` ─ `fano_inequality_measure_theoretic` (Fano/Measure.lean:224) を `(X, Y, decoder) := (Fin n → α, Fin M, d)` で `Yo := Yo_n` (= `c ∘ X^n`)、適用後 `decoder := d : Fin M → (Fin n → α)` で誤り率は `errorProb μ X^n Yo_n d = Pe_n`。**`hcard_Pi` を仮定形にあわせて `2 ≤ Fintype.card (Fin n → α)`**。20〜30 行
- [ ] **(B.5) Step E**: 簡略化 `Real.log ((Fintype.card α)^n - 1) ≤ n · Real.log (Fintype.card α)` ─ `Real.log_pow` + `Real.log_le_log` (引数 `≤` の monotonicity) + `(Fintype.card α)^n - 1 ≤ (Fintype.card α)^n`。10〜15 行
- [ ] **(B.6) 組成 Bridge → Phase A**: `H(X^n) = (mutualInfo μ X^n Yo_n).toReal + condEntropy μ X^n Yo_n` (`mutualInfo_eq_entropy_sub_condEntropy μ X^n Yo_n hX^n hYo_n` の rearrange)、Phase A `entropy_jointRV_eq_n_smul` で LHS = `n · entropy μ (Xs 0)`。Step A〜E を `linarith` で連結。20〜30 行

### Done 条件

- [ ] 上記 7 項目が silent
- [ ] proof-log + metrics 取得済み

### 工数感

3〜5 日 (80〜120 行)。**Slepian–Wolf converse `slepian_wolf_converse_X` (SlepianWolf.lean:217) と同形の plumbing**、前例あり。最大リスク: B.4 で `Fano/Measure.lean:224` の Fintype + MeasurableSingletonClass instance が `Fin n → α` で自動 derive するか (Han Phase D 前例より GO 見込み)。

### 撤退ライン (Phase B 内)

- B.4 で Fintype 自動 derive が破綻する場合 → `Pi.fintype` / `Pi.measurableSpace` / `Pi.instMeasurableSingletonClass` を明示的に `haveI` で渡す (前例: HanD.lean)。+5〜10 行で済む見込み
- B.5 の `Real.log_pow` plumbing で `(Fintype.card α : ℝ)^n` vs `((Fintype.card α)^n : ℝ)` の cast で詰まる場合 → `Nat.cast_pow` の simp lemma で normalise

---

## Phase C — `Filter.liminf` 形主定理 (`source_coding_converse`) 📋

### スコープ

```lean
namespace InformationTheory.Shannon

/-- **Source coding theorem, weak converse**:
For any block code `(c_n, d_n)` with `M_n` codewords and i.i.d. discrete source,
if the error probability vanishes then the rate is at least the entropy. -/
theorem source_coding_converse
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α)
    (M : ℕ → ℕ) (hM_pos : ∀ n, 0 < M n)
    (c : ∀ n, (Fin n → α) → Fin (M n))
    (d : ∀ n, Fin (M n) → (Fin n → α))
    (hPe_to_zero :
      Tendsto (fun n => InformationTheory.MeasureFano.errorProb μ
                          (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
              atTop (𝓝 0)) :
    entropy μ (Xs 0)
      ≤ Filter.liminf (fun n : ℕ => Real.log (M n : ℝ) / n) atTop

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(C.1) `δ_n := h(Pe_n) / n + Pe_n · log |α|`** の定義 + `Tendsto δ atTop (𝓝 0)`:
  - `Tendsto Pe atTop (𝓝 0)` (仮定 `hPe_to_zero`) ⟹ `Tendsto (Pe_n · log |α|) atTop (𝓝 0)` (`Filter.Tendsto.mul_const`)
  - `Tendsto (h ∘ Pe) atTop (𝓝 (h 0)) = 𝓝 0` (`Real.binEntropy_zero` + `Real.continuous_binEntropy.tendsto`)、`Tendsto (h ∘ Pe / n) atTop (𝓝 0)` (`Filter.Tendsto.div_atTop` の Nat 版 or `tendsto_const_nhds` * 1/n → 0)
  - `Tendsto (h(Pe_n)/n + Pe_n · log |α|) atTop (𝓝 0)` (Tendsto.add)
  - 20〜30 行
- [ ] **(C.2) per-n bound の `/n` 版**: Phase B `source_coding_per_n_bound` から `(n : ℝ) · H ≤ log M_n + h(Pe_n) + Pe_n · n · log |α|`、両辺 `/n` (n ≥ 1 で `(n : ℝ) > 0`) で
  ```
  H ≤ log M_n / n + h(Pe_n) / n + Pe_n · log |α|
    = log M_n / n + δ_n
  ```
  `eventually_atTop` (`∀ᶠ n in atTop, 1 ≤ n`) で plumbing。10〜15 行
- [ ] **(C.3) `liminf_le_liminf` 適用**: `∀ᶠ n in atTop, entropy μ (Xs 0) − δ_n ≤ log M_n / n` ⟹ `liminf (fun n => H − δ_n) atTop ≤ liminf (fun n => log M_n / n) atTop`。LHS は `Tendsto (H − δ_n) atTop (𝓝 H)` から `Filter.Tendsto.liminf_eq` で `H` に潰す。10〜15 行
- [ ] **(C.4) IsBoundedUnder / IsCoboundedUnder の `by isBoundedDefault`**: Mathlib デフォルトで通る (実数値、atTop)、要 spot 確認。0〜5 行

### Done 条件

- [ ] 上記 4 項目が silent
- [ ] `source_coding_converse` の statement が Cover-Thomas (Theorem 5.4.1) と一致
- [ ] proof-log + metrics 取得済み

### 工数感

2〜3 日 (50〜80 行)。**Stein converse Phase C の Tendsto squeeze plumbing と同形**、`Filter.liminf` API は inventory 軸 1 で完備確認済。最大リスク: C.4 の `isBoundedDefault` 周辺で IsCoboundedUnder の暗黙引数が `by isBoundedDefault` で解決しない場合、`Real.continuous_log` の bounded image 等で明示渡し +5〜10 行。

### 撤退ライン (Phase C 内)

- C.3 で `liminf_le_liminf` の `IsCoboundedUnder` 自動解決が破綻する場合 → `le_liminf_of_le` (`Mathlib/Order/LiminfLimsup.lean:145`) に切り替え (`∀ᶠ n in atTop, entropy μ (Xs 0) − δ_n ≤ log M_n / n` から `entropy μ (Xs 0) − δ_n` を `δ_n → 0` で `entropy μ (Xs 0)` に近づけ、`∀ ε > 0, ∀ᶠ n, entropy μ (Xs 0) − ε ≤ log M_n / n` の form に reshape して `le_liminf_of_le` を直接適用)、+10〜20 行
- C.1 で `Real.continuous_binEntropy.tendsto` が薄い場合 → `Real.binEntropy` の simp 展開で直接 `Tendsto (h ∘ Pe) atTop (𝓝 0)` を `Pe ≥ 0`, `Pe ≤ 1` の bounded sandwich で示す (5〜10 行)

---

## Phase D — verify 📋

### スコープ

- [ ] `lake env lean Common2026/Shannon/AEP.lean` (or 新ファイル) silent
- [ ] `lake build Common2026.Shannon.AEP` (or 新ファイル) 緑通過 (依存 module の olean refresh 確認)
- [ ] proof-log: `docs/proof-logs/proof-log-aep-source-coding.md` 起票
- [ ] metrics: `scripts/session_metrics.ts` 実行 + `docs/metrics/aep-source-coding.{manifest,metrics}.{json,md}` 出力
- [ ] `docs/moonshot-seeds.md` の "Seed 4 → A. AEP Phase D" 項目を ✅ 更新 + Phase E (achievability) 切り出し方針確認
- [ ] `docs/shannon/aep-moonshot-plan.md` の進捗を `Phase D ✅` に更新 (Phase E は別 plan に切り出し継続)

### Done 条件

- [ ] 全 5 項目完了

### 工数感

半日。

---

## 失敗判定 / 撤退ライン (全体)

| 撤退ポイント | 判定基準 | アクション |
|---|---|---|
| Phase 0 で源符号化定理が Mathlib にあった | 0 件確認済み (本 inventory 軸 4) | 不該当 |
| Phase A の A.4 Step 3 (Pi 値 reshape) で 3〜5 日溶ける | 進捗 0、`iIndepFun.indepFun_finset` の Pi reshape が plumbing-heavy | **代替路線**: `Han.jointEntropy_chain_rule` を直接呼んで induction 不要のラインに切り替え (20〜40 行で済む見込み) |
| Phase A の A.1 で `mutualInfo_eq_zero_iff_indep` が片向きしかなかった | 既存 statement を読んで判定 | 自前で逆向きを書き下ろす (mutualInfo 積分形 unfold、20〜30 行) |
| Phase B の B.4 で Fintype 自動 derive 破綻 | Han Phase D の `Fin n → α` Fintype instance 問題と同形 | `haveI` 明示渡しで +5〜10 行 |
| Phase C の C.3 で `IsCoboundedUnder` 自動解決破綻 | `liminf_le_liminf` の暗黙引数で `isBoundedDefault` failure | `le_liminf_of_le` に切り替え + `∀ ε > 0, ...` form に reshape (+10〜20 行) |
| **Phase A 完了 (= i.i.d. block entropy chain rule)** | `entropy_jointRV_eq_n_smul` silent | **★ 撤退ライン: 「i.i.d. block entropy の Pi 化 chain rule」が独立 publish 可能 ★**。Phase B/C を別 plan に切り出すかは Phase A 完了時点で判断 |
| Phase B 完了 (= per-n bound) | `source_coding_per_n_bound` silent | 撤退判断不要、Phase C へ |
| Phase C 完了 (= 主定理) | `source_coding_converse` silent | 完成 |

どのケースも proof-log に **正直に**記録。

---

## 工数見積もり総括

| 経路 | 工数 | 行数 | リスク |
|---|---|---|---|
| Phase A 単独 (i.i.d. block entropy chain rule) | **3〜5 日** | **80〜150 行** | **中** (A.4 Pi 値 reshape) |
| Phase A〜B (per-n bound 確定) | **6〜10 日** | **160〜270 行** | **中** |
| Phase A〜C (主定理) | **8〜13 日 = 1.5〜2 週** | **210〜350 行** | **中** |
| Phase A〜D (verify 込み) | **9〜14 日** | **210〜350 行** | **中** |

シード見積 **300〜500 行 / 中リスク / 1〜1.5 週間** とほぼ一致 (やや少なめ、`shannon_converse_single_shot` の uniform 仮定問題で骨格再演を選んだのが行数を増やすが、`entropy_le_log_card` 等の既存 4 部品再利用が大きく、SlepianWolf converse と同形 plumbing で進む)。

撤退時 (Phase A) でも **「i.i.d. block entropy chain rule」** が独立 publish ライン。「Pi 化 entropy = n · H(X)」は Mathlib にも不在の汎用補題で、Stein converse の `klDiv_pi_eq_n_smul` (i.i.d. KL chain rule) と並ぶ **上流 PR 候補**。

---

## 当面の next step

1. ✅ **Phase 0 (本 plan + inventory 起草)** — 完 (2026-05-11)
2. **Phase A skeleton** — `Common2026/Shannon/AEP.lean` (or 新ファイル `Common2026/Shannon/SourceCoding.lean`) の末尾に `condEntropy_eq_entropy_of_indepFun` / `entropy_eq_of_identDistrib` / `entropy_jointRV_eq_n_smul` を `:= by sorry` で append、緑通過確認 ← **次これ**
3. **Phase A 完で Phase B 着手判定** — `entropy_jointRV_eq_n_smul` が silent なら Phase B (per-n bound、Slepian–Wolf 流儀 4-step)
4. **Phase B 完で Phase C 着手判定** — `source_coding_per_n_bound` silent なら Phase C (主定理 + Filter.liminf)
5. **Phase C 完 = 完成**: proof-log + metrics 取得、Phase E (achievability) を別 plan に切り出すかは本 plan 完了時に判断

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-11 — 起草

- **`SourceCode` 構造体は導入しない**: inventory 軸 4 で確認、既存 `MeasureFano.errorProb` を直接利用。`SourceCode` ラッパーは plumbing コスト + 命名衝突リスク、Slepian–Wolf converse の流儀 (encoder / decoder を直接引数で受ける) と整合
- **`shannon_converse_single_shot` 直接呼びは諦める**: inventory 軸 5 で確認、uniform `Msg` 仮定が `X^n` で破綻 (Xs 0 が uniform でなければ `X^n` も非 uniform)。代わりに **骨格再演** (Slepian–Wolf converse `slepian_wolf_converse_X` と同形の 4-step assembly) を採用
- **i.i.d. 仮定を `Pairwise IndepFun` から `iIndepFun` に強化**: inventory 軸 2 で確認、`H(X^n) = n · H(X)` には mutual independence が必要 (Bernstein counterexample)。AEP Phase A〜C は `iIndepFun.indepFun` で自動 lift できるので caller 負担は仮定 1 本の置換のみ
- **ファイル分割は Phase A 着手時に判断**: AEP.lean が 432 行、Phase A〜C で +210〜350 行 = 642〜782 行。800 行を超えそうなら `Common2026/Shannon/SourceCoding.lean` 新ファイル、`import Common2026.Shannon.AEP` で受ける
- **Phase A の代替路線 (`Han.jointEntropy_chain_rule` 直接利用)** を撤退ラインに準備: A.4 Step 3 (Pi 値 reshape) で詰まる場合の主路線として、induction 不要で済む可能性が高い (Phase A 着手時に主路線・代替路線のどちらがクリーンか実装後判断)

### 2026-05-11 — 実装完了 (Phase A〜D ✅)

- **Phase A: Han 路線採用** (撤退ライン準備していたが、direct 帰納より plumbing が薄く第一選択になった)。Pi 値 reshape は `iIndepFun.indepFun_finset` を **`ℕ`-indexed `Xs` 上で `S = {i}, T = Finset.range i`** に取って `IndepFun.comp` で `(Xs i, prefix)` に投影する形で `Fin n` 内 reshape を回避。Han Phase D の自前 `MeasurableEquiv` (`fullSplitMEquiv` 等) より大幅に短い、後続 moonshot で再利用候補
- **Phase B: Step C (DPI postprocess) は assembly 上不要**だったため省略。`fano_inequality_measure_theoretic` を直接 `condEntropy μ Xn Yn` に当てる方が clean。Slepian-Wolf converse とは bound 形が異なる点 (Slepian-Wolf は side info entropy で reshape するため DPI 経由が必要だが、source coding は単一 RV で完結)
- **Phase C: 仮定 `hM_bdd : ∃ R, ∀ n, log M_n / n ≤ R` を入口に追加**。`Filter.liminf_le_liminf` / `le_liminf_of_le` が `IsCoboundedUnder (· ≥ ·)` を要求し、これは実数値 unbounded sequence で auto では通らない (Mathlib `sSup ℝ = 0` 規約により collapse)。`IsCoboundedUnder.of_frequently_le` で discharge。**Phase 0 inventory 軸 1 「Filter.liminf 完備」記述の見落とし** (cobounded semantics の condition 言及なし)。`EReal.liminf` 化代案 (+30〜50 行) も検討したが、statement 全体に EReal coercion が波及するため不採用。実用 (`M_n = 2^⌈nR⌉` rate-bounded codes) では `hM_bdd` は caller 1 行で trivial に提供可能
- **`Tendsto.mul_const` は `Filter.Tendsto.mul_const` という名前では存在しない**。`ENNReal.Tendsto.mul_const` のみ。代わりに `.mul tendsto_const_nhds` を組成
- **行数 +368 (target 210-350 を 18 行超過)**: 主因は (a) `hM_bdd` 周辺の `IsCoboundedUnder` discharge、(b) `δ_n := h(Pe_n)/n + Pe_n · log|α|` の `Tendsto _ (𝓝 0)` 証明 (`binEntropy_continuous` + `tendsto_one_div_atTop_nhds_zero_nat` + `Tendsto.mul/add`)。ceiling 450 内で許容範囲

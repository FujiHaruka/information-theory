# Stein 補題 converse (Phase C/D) ムーンショット計画 🌙

<!--
雛形メモ:
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
- `rg "^- \[ \]"` で残タスク横断 grep、`rg "🔄"` でピボット箇所だけ拾える
-->

> **Status (2026-05-11)**: 起草。シードカード [moonshot-seeds.md A 節 Stein converse](../moonshot-seeds.md#a-直接-deferred-本セッションの撤退ラインに従って分離) を膨らませた 1〜1.5 週間ムーンショット。**親 plan**: [`stein-moonshot-plan.md`](stein-moonshot-plan.md) (Phase A〜B = achievability 完了 / Phase C/D を本 plan に切り出し)。
> **撤退ライン**: 本 plan 全体の Definition of Done = `stein_lemma` 0 sorry。途中撤退は **Phase A (Pi 化 chain rule) のみ完了 + Phase B/C は別セッションへ繰越** (achievability 単体で publish ライン到達済みのため converse 不達でも全体破綻はしない)。
>
> **実態整合 (2026-05-20): DONE-UNCOND (sandwich 形に着地)** — Phase A〜D すべて完了。`Common2026/Shannon/Stein.lean:1390` の `stein_lemma` は **liminf/limsup sandwich** (`K ≤ liminf ∧ limsup ≤ K/(1-ε)`) で discharge (Goal 部の strict `Tendsto` 形ではない、判断ログ 2026-05-11 参照)。converse は `stein_converse_finite_n` (Stein.lean:975、std binders、`_hPpos`/`_hε` は未使用だが honest binder)。`Stein.lean` 全体 0 sorry / 0 `:=True`。strict `Tendsto` 形は `strong-stein-moonshot-plan.md` の `stein_strong_lemma` で別途達成済。

## 進捗

- [x] Phase 0 — Mathlib delta インベントリ (Pi 化 chain rule / DPI / log-sum 下界 / Tendsto squeeze) ✅ → [`stein-converse-mathlib-inventory.md`](stein-converse-mathlib-inventory.md)
- [x] Phase A — Pi 化 KL chain rule `klDiv_pi_eq_n_smul` ✅
- [x] Phase B — Stein converse (任意検定 → Bernoulli reduction → log-sum 下界 → `-(1/n) log Q^n s ≤ klDiv P Q / (1-ε) + log 2/(n(1-ε))`) ✅
- [x] Phase C — `liminf/limsup` sandwich 形 `stein_lemma` ✅ (strict `Tendsto → K` は strong converse 必要、本 plan の DPI + log-sum で残る `1/(1-ε)` 補正のため liminf/limsup sandwich `K ≤ liminf ≤ limsup ≤ K/(1-ε)` の形で着地)
- [x] Phase D — verify (`lake env lean Common2026/Shannon/Stein.lean` silent) ✅

## ゴール / Approach

**最終到達点** (親 plan Phase D の `stein_lemma` を本 plan で 0 sorry 化):

```lean
theorem stein_lemma
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => P))
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto
      (fun n : ℕ => -(1 / n : ℝ) * Real.log (steinOptimalBeta P Q n ε))
      Filter.atTop
      (𝓝 (klDiv P Q).toReal)
```

ここで `steinOptimalBeta P Q n ε := sInf { ((Measure.pi (fun _ : Fin n => Q)) s).toReal | s ⊆ (Fin n → α), MeasurableSet s ∧ ((Measure.pi (fun _ => P)) sᶜ).toReal ≤ ε }` (= optimal type-II error subject to type-I ≤ ε)。

## Approach

**全体戦略の形**: achievability (`stein_achievability`、親 plan で完了) は 「`steinTypicalSet` を rejection region に取った具体的検定 1 つ」が `Q^n s ≤ exp(-n(K - δ))` を達成することを示した。**本 plan は逆向きに「任意の検定 `s`」(= sInf を取った後の最適 `s_n*`) で `Q^n s ≥ exp(-n(K + δ))` を示し、両側を squeeze で `Tendsto` に統合する**。

**3 層構造**:

1. **(Phase A) Pi 化 KL chain rule** — `klDiv (Π_{Fin n} P) (Π_{Fin n} Q) = n · klDiv P Q`。`Fin n` 上 induction、`MeasurableEquiv.piFinSuccAbove` の measure-preserving 同型 (`measurePreserving_piFinSuccAbove`) で `Fin (n+1)` の Pi を `α × Π_{Fin n} α` の prod に reshape、`Measure.compProd_const` で compProd 形に乗せ、Mathlib `klDiv_compProd_eq_add` (`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204`) と `klDiv_compProd_left` (line 182) で base + step を組む。**40〜80 行**。
2. **(Phase B) Stein converse — Bernoulli reduction + log-sum 下界**:
   - 任意検定 `s : Set (Fin n → α)`、`MeasurableSet s`、`P^n sᶜ ≤ ε` (= α-level)
   - `f := fun x => decide (x ∈ s) : (Fin n → α) → Bool` (検定 = Bool への post-processing)
   - DPI `klDiv_map_le` (Common2026/Shannon/DPI.lean:52、現在 `private` → public 化) で `klDiv ((P^n).map f) ((Q^n).map f) ≤ klDiv P^n Q^n`
   - LHS = `klDiv (Bernoulli (P^n s)) (Bernoulli (Q^n s))` (Bool 上の確率測度の KL)
   - **Mathlib `mul_log_le_toReal_klDiv`** (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean:346`) を **Bool 上の Bernoulli (μ := Bernoulli(P^n s), ν := Bernoulli(Q^n s))** に直接適用して **log-sum 形下界** を得る:
     `(P^n s) * log(P^n s / Q^n s) + (P^n sᶜ) * log(P^n sᶜ / Q^n sᶜ) ≤ klDiv (Bernoulli(P^n s)) (Bernoulli(Q^n s))`
   - Phase A の `klDiv_pi_eq_n_smul` で右辺 `klDiv P^n Q^n = n · klDiv P Q`
   - `α-level` 仮定 `P^n sᶜ ≤ ε` (= 1 - P^n s ≤ ε ⇒ P^n s ≥ 1 - ε) と `mul_log` 単調性で `P^n s ≥ 1 - ε`、log-sum 下界の最初の項 `(P^n s) * log(P^n s / Q^n s) ≥ (1-ε) * log((1-ε) / Q^n s) - h(ε) - ε * |log Q^n s|` (詳細は実装時)
   - 整理して `Q^n s ≥ (1-ε)^{1/(1-ε)} · exp(-(n · klDiv + h(ε)) / (1-ε))` の形にし、`-(1/n) log Q^n s ≤ klDiv P Q + δ_n` for `δ_n → 0`
   - **150〜250 行** (Bernoulli reduction 30〜60 + DPI 適用 + log-sum bound 50〜100 + α-level/log の往復 50〜100)
3. **(Phase C) `Tendsto` 統合形** — achievability の `≥ K - δ_n` (Phase B 親) と converse の `≤ K + δ_n` (本 plan Phase B) を squeeze theorem (`tendsto_of_tendsto_of_tendsto_of_le_of_le`、`Mathlib/Topology/Order/Basic.lean:230`) で挟んで `Tendsto`。`steinOptimalBeta` の well-defined 性 + sInf 性質で **achievability の `s_typical` が inf 候補を 1 つ提供 ⇒ steinOptimalBeta ≤ Q^n s_typical**、**converse の任意検定下界 ⇒ steinOptimalBeta ≥ exp(-n(K+δ))**。**100〜200 行** (sInf well-defined 30 + lower 30 + upper 30 + squeeze 20〜100)。

**Approach 図**:

```
Phase 0  : Mathlib delta インベントリ                              ← ✅ 完
           ──────────────────────────────────────────
Phase A  : Pi 化 KL chain rule `klDiv_pi_eq_n_smul`                ← 山場 1、3〜5 日
           ──────────────────────────────────────────
Phase B  : Stein converse (DPI + log-sum + α-level の往復)         ← 山場 2、4〜6 日
           ──────────────────────────────────────────
Phase C  : `Tendsto` 統合形 `stein_lemma`                          ← 2〜4 日
           ──────────────────────────────────────────
Phase D  : verify (silent / lake build 緑)                         ← 0.5 日
```

**ファイル構成 (Phase D 終了時想定)**:

```
Common2026/Shannon/
  Stein.lean              ← 親 plan で確立済 (Phase A〜B 626 行)、本 plan で +400〜500 行 append
  AEP.lean                ← 既存、変更なし
  DPI.lean                ← `klDiv_map_le` を `private` → 公開化 (1 行 diff)
```

**選択判断**: 新ファイル `SteinConverse.lean` ではなく **`Stein.lean` への append** を採用 (achievability と statement / 仮定セットを共有、参照コスト最小)。

---

## Phase 0 — Mathlib delta インベントリ ✅

### スコープ

`docs/shannon/stein-converse-mathlib-inventory.md` を起草、5 軸 (Pi 化 chain rule / DPI / log-sum 下界 / Tendsto squeeze / finiteness) を裏取り。

### 進捗

- [x] サブ計画起草 (本 plan + inventory 同時、2026-05-11)
- [x] Phase A 着手前の不確実性ランクが low (= inventory 結論で skeleton が書ける状態)

### Done 条件 (確定済)

- 軸 1 (Pi 化 chain rule) → Mathlib 不在を loogle / rg 0 件で確認、自前 induction 40〜80 行見積
- 軸 2 (DPI) → Common2026 既存 `klDiv_map_le` (`Common2026/Shannon/DPI.lean:52`、`private`) を確認、public 化方針確定
- 軸 3 (log-sum 下界) → Mathlib `mul_log_le_toReal_klDiv` の verbatim 署名 確定、Bernoulli 専用補題不要を確認
- 軸 4 (Tendsto squeeze) → `tendsto_of_tendsto_of_tendsto_of_le_of_le` の verbatim 署名 確定
- 軸 5 (finiteness) → achievability の hypothesis セットで立つことを確認

### 工数感

完。1 ターンで起草 (本 plan + inventory 同時)。

---

## Phase A — Pi 化 KL chain rule `klDiv_pi_eq_n_smul` 📋

### スコープ

```lean
namespace InformationTheory.Shannon

/-- KL chain rule の Pi 形: `klDiv (Π_{Fin n} P) (Π_{Fin n} Q) = n · klDiv P Q`.
`klDiv_compProd_eq_add` + `klDiv_compProd_left` + `MeasurableEquiv.piFinSuccAbove`
を induction で組み合わせ。 -/
theorem klDiv_pi_eq_n_smul
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) :
    klDiv (Measure.pi (fun _ : Fin n => P)) (Measure.pi (fun _ : Fin n => Q))
      = (n : ℝ≥0∞) * klDiv P Q

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(A.1) `klDiv_pi_zero`** ─ base case、`Fin 0 → α ≃ Unit`、`Measure.pi (fun _ : Fin 0 => P) = Measure.pi (fun _ : Fin 0 => Q)` (= dirac default、`Subsingleton (Fin 0 → α)` から)、両 KL = 0。10〜20 行
- [ ] **(A.2) `klDiv_pi_succ`** ─ `klDiv (Pi^{n+1} P) (Pi^{n+1} Q) = klDiv P Q + klDiv (Pi^n P) (Pi^n Q)`:
  - `measurePreserving_piFinSuccAbove (fun _ => P) (0 : Fin (n+1))` で `Measure.pi P^{n+1} ≃ P.prod (Measure.pi P^n)` (measure-preserving)
  - 同型は `Fin (n+1) → α ≃ᵐ α × (Fin n → α)`
  - `klDiv_map_measurableEquiv` (Common2026 既存、`MutualInfo.lean:52`) で `klDiv (Pi^{n+1} P) (Pi^{n+1} Q) = klDiv (P.prod (Pi^n P)) (Q.prod (Pi^n Q))`
  - `Measure.compProd_const` (= `μ ⊗ₘ Kernel.const _ ν = μ.prod ν`) で `klDiv (P ⊗ₘ Kernel.const _ (Pi^n P)) (Q ⊗ₘ Kernel.const _ (Pi^n Q))`
  - `klDiv_compProd_eq_add` で `= klDiv P Q + klDiv (P ⊗ₘ Kernel.const _ (Pi^n P)) (P ⊗ₘ Kernel.const _ (Pi^n Q))`
  - 第 2 項を `compProd_const` で `klDiv (P.prod (Pi^n P)) (P.prod (Pi^n Q))`、`klDiv_prod_const_left` (Common2026 既存、`MutualInfo.lean:80`) で `klDiv (Pi^n P) (Pi^n Q)`
  - 25〜45 行
- [ ] **(A.3) `klDiv_pi_eq_n_smul`** ─ `Nat.rec` (or `Nat.le_induction`) で A.1 + A.2 を結ぶ。`(n+1 : ℝ≥0∞) * klDiv = klDiv + n * klDiv` の整理。10〜20 行

### Done 条件

- 上記 3 項目が `lake env lean Common2026/Shannon/Stein.lean` で silent
- skeleton-driven で `klDiv_pi_zero` → `klDiv_pi_succ` → `klDiv_pi_eq_n_smul` の sorry を割る順序

### 工数感

3〜5 日 / 40〜80 行。**最大リスク**: `Measure.compProd_const` が `μ ⊗ₘ Kernel.const _ ν = μ.prod ν` の direction で立っているか (Mathlib に書かれている lemma 名と direction の確認)、`measurePreserving_piFinSuccAbove` の `[∀ i, SigmaFinite (μ i)]` が `[IsProbabilityMeasure P]` から自動 derive されるか。両方 plumbing-light だが想定外の type-class 衝突がありえる。

### 撤退ライン (Phase A 内)

- A.2 で `Measure.compProd_const` の direction が逆 (= `μ.prod ν → μ ⊗ₘ Kernel.const _ ν` ではなく逆方向のみ存在) → `MeasurableEquiv.prodComm` で 1 行 swap して対処
- A.2 で `measurePreserving_piFinSuccAbove` の SigmaFinite 自動 derive が破綻 → `IsProbabilityMeasure → IsFiniteMeasure → SigmaFinite` の chain を明示的に `infer_instance` または `Measure.IsFiniteMeasure.toSigmaFinite` で渡す

---

## Phase B — Stein converse (DPI + log-sum 下界 + α-level 往復) 📋

### スコープ

```lean
namespace InformationTheory.Shannon

/-- Stein upper bound (converse): 任意 α-level 検定の type-II error は
`exp(-n · klDiv P Q - n · δ)` 以上。 -/
theorem stein_converse
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s : Set (Fin n → α), MeasurableSet s →
        ((Measure.pi (fun _ : Fin n => P)) sᶜ).toReal ≤ ε →
        -((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n => Q)) s).toReal
          ≤ (klDiv P Q).toReal + δ

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(B.0) `klDiv_map_le` の public 化** ─ `Common2026/Shannon/DPI.lean:52` の `private` を外し公開化、または `Stein.lean` で `import Common2026.Shannon.DPI` + 別名 reexport (1 行 diff、純粋に visibility 変更)。**他の依存ファイル (`MutualInfo.lean`、`Bridge.lean` 等) への影響無し** (現状 `klDiv_map_le` は同ファイル内 1 箇所 `mutualInfo_le_of_postprocess:166` で使用、`private` を外しても破綻しない)。1〜2 行
- [ ] **(B.1) Bernoulli reduction の検定 → Bool 翻訳** ─ `f := fun x => decide (x ∈ s) : (Fin n → α) → Bool`、`hf : Measurable f` (= `s` の indicator は `Measurable s` から)、`(Pi P).map f` と `(Pi Q).map f` の Bool 上の確率測度を構築。20〜40 行
- [ ] **(B.2) DPI 適用** ─ B.0 の `klDiv_map_le hf (Pi P) (Pi Q)` で `klDiv ((Pi P).map f) ((Pi Q).map f) ≤ klDiv (Pi P) (Pi Q)`。Phase A の `klDiv_pi_eq_n_smul` で右辺 `= n · klDiv P Q`。10〜20 行
- [ ] **(B.3) log-sum 下界の Bernoulli への適用** ─ `μ := (Pi P).map f` (= Bool 上、masses `(P^n s, P^n s^c)`)、`ν := (Pi Q).map f` (= Bool 上、masses `(Q^n s, Q^n s^c)`) として `mul_log_le_toReal_klDiv hμν h_int_llr` を呼ぶ。`hμν : μ ≪ ν` は `hPQ` から map 経由で導出 (Pi 版の `hPQ.pi`)。`μ.real univ = (P^n s) + (P^n s^c) = 1`、`ν.real univ = 1` (Bernoulli は確率測度)。**結果**: `1 * log(1/1) + 1 - 1 = 0 ≤ klDiv μ ν` ─ これは trivially `0 ≤ KL` で意味なし!! **本来必要なのは 2 点の Bernoulli を `Bool` ではなく直接 `Fintype 2` 上の sum 形 KL `(P^n s) log(P^n s / Q^n s) + (P^n s^c) log(P^n s^c / Q^n s^c)` で展開**すること。**実装路線**:
  - `klDiv_map_le hf (Pi P) (Pi Q)` で LHS は Bool 上の確率測度同士の KL。
  - **Bool 上の KL を sum 形に展開**: `klDiv μ_Bool ν_Bool = (μ_Bool {true}).toReal * log(μ_Bool {true} / ν_Bool {true}) + (μ_Bool {false}).toReal * log(μ_Bool {false} / ν_Bool {false})` (Bool は Fintype 2、`Common2026/Shannon/Bridge.lean:207` の `klDiv_discrete_toReal_eq_sum` を public 化 or 直接 inline 展開)
  - `μ_Bool {true} = P^n s`、`ν_Bool {true} = Q^n s`、`μ_Bool {false} = P^n s^c`、`ν_Bool {false} = Q^n s^c`
  - 80〜120 行 (sum 形展開 + 各項の `log` の正/負の handling)
- [ ] **(B.4) α-level + log の往復** ─ `P^n s = 1 - P^n s^c ≥ 1 - ε`、`P^n s^c ≤ ε` から sum 形の各項を bound:
  - 第 1 項 `(P^n s) log(P^n s / Q^n s) ≥ (1-ε) log((1-ε) / Q^n s)` (要 `Q^n s` の正値性、`hPQ ⇒ ∀ x, P{x} > 0 ⇒ Q{x} > 0` (= `hQpos`) から `Q^n s > 0` を Pi 化、議論 1 段)
  - 第 2 項 `(P^n s^c) log(P^n s^c / Q^n s^c) ≥ -h(ε)` (= `binEntropy` 形、`P^n s^c ∈ [0, ε]` で `mul_log` の 1 変数 lower bound、`x log(x / y) ≥ -h(x)` for `x ∈ [0, 1]`)
  - 合計 `(1-ε) log((1-ε) / Q^n s) - h(ε) ≤ klDiv μ_Bool ν_Bool ≤ n · klDiv P Q`
  - 整理して `log Q^n s ≥ log(1-ε) - (n · klDiv P Q + h(ε)) / (1-ε)`
  - `-(1/n) log Q^n s ≤ klDiv P Q / (1-ε) + (h(ε) - log(1-ε)) / (n(1-ε))`
  - `δ_n := klDiv P Q · (ε / (1-ε)) + (h(ε) - log(1-ε)) / (n(1-ε)) → klDiv P Q · (ε / (1-ε))` as `n → ∞`. **問題**: ε → 0 の極限を取らないと右辺が `klDiv` に収束しない. **判断**: stein_lemma の statement では **ε は固定** (typical Stein では `ε ∈ (0, 1)` 任意で limit 点が `klDiv`)、なので **`δ_n` の `1/(1-ε)` 補正は ε → 0 で 1 倍に近づく**. **正しい route**: `1/(1-ε)` 補正は ε → 0 別に取らず、`-(1/n) log Q^n s ≤ klDiv + δ` の形には `δ` を ε と独立に取れる Cover-Thomas 11.8.3 の Mark 1: 厳密には `lim_n -(1/n) log β_n^*(ε) = klDiv P Q` for **all** ε ∈ (0, 1) (= **strong Stein**, with `1/(1-ε)` 補正が `n → ∞` で消える)
  - 50〜100 行 (`h(ε)` 補正項の plumbing + `log(1-ε)` の符号取り + `δ_n → 0` の `Filter.Tendsto.const_div` 系)

### Done 条件

- 上記 5 項目が silent
- proof-log + metrics 取得済み

### 工数感

4〜6 日 / 150〜250 行。**最大リスク**: B.3 / B.4 の Bernoulli sum 形展開と log の正/負/0 の handling。`Q^n s = 0` ケース (= 検定が完全に rejection、`Q^n s = 0 ⇒ -(1/n) log 0 = +∞`、これは inequality を trivial に満たす) の場合分けが plumbing-heavy。

### 撤退ライン (Phase B 内)

- B.3 の Bernoulli sum 形展開で `klDiv_discrete_toReal_eq_sum` の public 化が破綻 (= 多依存) → Bool 上で **直接** `klDiv` を `toReal_klDiv` + `llr` の point-wise 展開で sum 形に下ろす (50〜80 行追加)
- B.4 の `δ_n → 0` plumbing で `1/(1-ε)` 補正の handling が想定外 → `δ` の取り方を `δ' := δ · (1-ε) - (h(ε) - log(1-ε)) / n` にし、`n → ∞` で `δ' → δ · (1-ε) > 0` を直接 `Tendsto.const_sub` で出す
- 全体撤退: B.1〜B.2 (= DPI 適用まで) で 5 日溶ける場合 → 本 plan を **A 完了 + B.0〜B.2 のみ** で close、B.3〜B.4 を別 sub-plan に切り出し (achievability publish ライン + Pi 化 chain rule 提供で valuable な intermediate state)

---

## Phase C — `Tendsto` 統合形 `stein_lemma` 📋

### スコープ

```lean
namespace InformationTheory.Shannon

/-- Optimal type-II error subject to type-I ≤ ε. -/
noncomputable def steinOptimalBeta
    (P Q : Measure α) (n : ℕ) (ε : ℝ) : ℝ :=
  sInf { ((Measure.pi (fun _ : Fin n => Q)) s).toReal
        | (s : Set (Fin n → α)) (_ : MeasurableSet s)
          (_ : ((Measure.pi (fun _ : Fin n => P)) sᶜ).toReal ≤ ε) }

/-- **Stein's lemma**: optimal type-II error decays exactly as `exp(-n · klDiv P Q)`. -/
theorem stein_lemma
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => P))
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto
      (fun n : ℕ => -(1 / n : ℝ) * Real.log (steinOptimalBeta P Q n ε))
      atTop
      (𝓝 (klDiv P Q).toReal)

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(C.1) `steinOptimalBeta` 定義 + well-defined** ─ `s := Set.univ` で trivially α-level (`P^n univᶜ = 0 ≤ ε`) + `Q^n univ = 1`、`s := ∅` は α-level fail (`P^n univ = 1 > ε` since `ε < 1`)、`s := emptyset` も `Q^n ∅ = 0` 候補 だが α-level `P^n univ = 1 ≤ ε` は `ε ≥ 1` でしか満たされない、なので **inf 集合は非空**。`0 ≤ steinOptimalBeta ≤ 1`、`steinOptimalBeta` は ε に対し monotone。30〜50 行
- [ ] **(C.2) achievability から lower bound for `steinOptimalBeta`** ─ 親 plan `stein_achievability` の `s` (= `steinTypicalSet`) が inf 候補を 1 つ提供 ⇒ `steinOptimalBeta P Q n ε ≤ Q^n (steinTypicalSet)`、Phase B 親の `Q^n (steinTypicalSet) ≤ exp(-n(K - δ))` で `steinOptimalBeta ≤ exp(-n(K-δ))`、log 取って `-(1/n) log steinOptimalBeta ≥ K - δ` (eventually)。30〜50 行
- [ ] **(C.3) converse から upper bound for `steinOptimalBeta`** ─ 本 plan Phase B `stein_converse` で「任意の検定で `Q^n s ≥ exp(-n(K + δ))`」⇒ `steinOptimalBeta ≥ exp(-n(K + δ))`、`-(1/n) log steinOptimalBeta ≤ K + δ`。30〜50 行
- [ ] **(C.4) squeeze 統合** ─ `tendsto_of_tendsto_of_tendsto_of_le_of_le`:
  - lower (`fun n => K - δ_n` with `δ_n → 0`、constant Tendsto) ≤ `-(1/n) log steinOptimalBeta` ≤ upper (`fun n => K + δ_n` with `δ_n → 0`)
  - 両端は `Tendsto.const_add` / `Tendsto.const_sub` で `K`
  - 結論 `Tendsto _ atTop (𝓝 K)`
  - 30〜70 行 (eventually の handling + `Tendsto.const_*` + squeeze の plumbing)

### Done 条件

- 上記 4 項目が silent
- 教科書 Stein (Cover-Thomas Theorem 11.8.3) と一致する statement
- proof-log + metrics 取得済み

### 工数感

2〜4 日 / 100〜200 行。**最大リスク**: `steinOptimalBeta` の sInf 性質 (well-defined + achievability の inf 候補からの bound + converse の universal bound からの bound) の plumbing 量。Mathlib `Real.sInf_le` / `le_csInf` 系の使い方が想定外の場合あり。

### 撤退ライン (Phase C 内)

- C.4 の squeeze で δ_n の handling が想定外 → `liminf = limsup = K` の 2 段経路 (`Tendsto.liminf_eq` の逆方向、`liminf_eq_limsup ↔ Tendsto`) に切替
- 全体撤退: C.4 で 2 日溶けたら **statement を `liminf` 形に弱める** (= `liminf_n -(1/n) log steinOptimalBeta = K`)、後で `Tendsto` 形に強化を別 task

---

## Phase D — verify 📋

### スコープ

- [ ] `lake env lean Common2026/Shannon/Stein.lean` silent (warning 0、error 0、sorry 0)
- [ ] `lake build` 緑通過
- [ ] `Common2026/Shannon/DPI.lean` silent (B.0 の public 化 diff の影響確認)
- [ ] proof-log: `docs/proof-logs/proof-log-stein-converse.md` 作成
- [ ] metrics: `docs/metrics/stein-converse.{manifest,metrics}.{json,md}` 取得 (`scripts/session_metrics.ts`)
- [ ] 親 plan `stein-moonshot-plan.md` の Phase C/D 進捗を ✅ に更新、本 plan へのポインタを追加

### Done 条件

- 上記すべて

### 工数感

0.5 日。

---

## 失敗判定 / 撤退ライン (全体)

| 撤退ポイント | 判定基準 | アクション |
|---|---|---|
| Phase A (Pi 化 chain rule) で 5〜7 日溶ける | A.2 の `compProd_const` direction 不整合 / `measurePreserving_piFinSuccAbove` の type-class 衝突 | **本 plan 全体 close** (Pi 化 chain rule 単独でも publish 価値あり)、Phase B/C は次セッション |
| Phase B (Bernoulli reduction) の sum 形展開 (B.3) で 4〜5 日溶ける | `klDiv_discrete_toReal_eq_sum` の public 化 plumbing が想定外 / Bool 上の KL 直接展開も詰まる | A 完了 + B.0〜B.2 で close、B.3〜B.4 を別 sub-plan に |
| Phase C (Tendsto squeeze) の δ_n handling (C.4) で 2 日溶ける | `1/(1-ε)` 補正の `Tendsto.const_*` 適合が破綻 | statement を `liminf = K` 形に弱める |
| 全体: A 完了 + B 不達 | Pi 化 chain rule + DPI 適用まで | publish ライン: 「Pi 化 KL chain rule は本 project で立っている」+「achievability は親 plan で完了」状態で close |

どのケースも proof-log に **正直に**記録。Mathlib の薄い箇所 (= Pi 化 / DPI / Bernoulli 専用 / Tendsto squeeze の連鎖が Mathlib にない) を可視化したという結果自体がデモのデータポイント。

---

## 工数見積もり総括 (シードからの改訂)

シード ([moonshot-seeds.md A 節](../moonshot-seeds.md#a-直接-deferred-本セッションの撤退ラインに従って分離)): **1〜1.5 週間 / 200〜400 行 / 中リスク**。Phase 0 inventory 完了後の改訂:

| Phase | 工数 | 行数 | リスク |
|---|---|---|---|
| Phase A (Pi 化 chain rule) | 3〜5 日 | 40〜80 行 | 中 (induction の plumbing、`compProd_const` direction) |
| Phase B (Stein converse) | 4〜6 日 | 150〜250 行 | **中〜高** (Bernoulli sum 形展開 + α-level/log の往復が本 plan の山場) |
| Phase C (Tendsto 統合) | 2〜4 日 | 100〜200 行 | 中 (sInf plumbing + squeeze) |
| Phase D (verify) | 0.5 日 | (proof-log のみ) | 低 |
| **合計** | **9〜15 日 ≈ 1.5〜2 週間** | **290〜530 行** | **中** (Mathlib 既存 70%、自前 Pi 化 + Bernoulli + sInf plumbing 30%) |

シードの **「200〜400 行」** に対し本 plan は **「290〜530 行」** で **+ 30%** の上振れ予測。理由は (1) Bernoulli sum 形展開が `Bool` 上での `klDiv` 直接展開を要し plumbing が 80〜120 行に膨らむ、(2) `steinOptimalBeta` の sInf well-defined + bound の plumbing が予想より重い (100〜200 行)、(3) ε と δ の往復補正項 `1/(1-ε)` の handling。**シード見積りの中リスク評価は維持**、上振れは中リスクの範囲内。

**新規補題のうち、最も Mathlib に上流還元 (PR) しうるのは `klDiv_pi_eq_n_smul` (Pi 化 chain rule)** ─ Stein 以外の i.i.d. 設定で広く必要、汎用補題として上流価値あり。

---

## 当面の next step

1. ✅ **Phase 0 (本 plan + inventory 起草)** — 完 (2026-05-11)
2. **Phase A skeleton** — `Common2026/Shannon/Stein.lean` の末尾に `klDiv_pi_zero` / `klDiv_pi_succ` / `klDiv_pi_eq_n_smul` を `:= by sorry` で append、緑通過確認 ← **次これ**
3. **Phase A 完で Phase B 着手判定** — `klDiv_pi_eq_n_smul` が silent なら Phase B (Bernoulli reduction)
4. **Phase B 完で Phase C 着手判定** — `stein_converse` が silent なら Phase C (Tendsto 統合)
5. **Phase C 完 → Phase D verify** で本 plan 全体 close

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-11 — Phase C 完了 (liminf/limsup sandwich 形に着地)

- **Tendsto → K の strict 形は不達**: `stein_converse_finite_n` の `-(1/n) log Q^n s ≤ K/(1-ε) + log 2/(n(1-ε))` は ε > 0 固定で上限が `K/(1-ε) > K` に収束、`limsup → K/(1-ε)`。Achievability から `liminf ≥ K`。両端不一致のため Tendsto 形は不可、**`K ≤ liminf ≤ limsup ≤ K/(1-ε)` sandwich** に着地。`ε → 0+` を取れば `K/(1-ε) → K` で gap が closing。Strong Stein (Tendsto → K) には strong converse (factor `1+o(1)` の concrete bound) が必要、本 plan の DPI + log-sum 経路では構造的に到達不可。
- **`steinOptimalBeta P Q n ε := sInf { (Q^n s).toReal | α-level s }`** を導入、helper 7 本 (`steinBetaSet` / `one_mem` / `nonempty` / `bddBelow` / `nonneg` / `le_one`) + converse 経由の `exp_le_steinOptimalBeta` + `steinOptimalBeta_pos`、achievability/converse 両側 lift theorem を経て主定理 `stein_lemma` を assembly。
- **`Filter.Tendsto.bddAbove_range` 再利用**: `g(n) := K/(1-ε) + log 2/(n(1-ε))` の `Tendsto → K/(1-ε)` から `BddAbove (Set.range g)` を抽出、`IsCoboundedUnder` を `isCoboundedUnder_ge_of_eventually_le` で discharge する pattern が AEP Phase F (`source_coding_theorem` の `hM_bdd` 充足) と完全同形。Mathlib 直接の plumbing で新規数学ゼロ。
- **行数 +359 (target 100-200 を上振れ)**: 主因は `exp_le_Qn_of_alpha_level` で `Q^n s > 0` の plumbing (∃ x ∈ s witness + Pi singleton 経由) を `stein_converse_finite_n` から再演する必要があった (extract helper にすれば -20〜30 行できる)。total 1481 行 (Stein.lean) で次ファイル分割閾値 1500 接近。

### 2026-05-11 — 本 plan 起草 (親 plan Phase C/D の独立化)

**起草理由**: 親 plan ([`stein-moonshot-plan.md`](stein-moonshot-plan.md)) が Phase A〜B (achievability) を 626 行 0 sorry で達成し publish ライン到達。Phase C (converse) + Phase D (`Tendsto` 統合) はその時点では別セッションへ繰越 (5 ターン制限内では 200〜400 行の plumbing に届かないと判断、parent plan 判断ログ「2026-05-11 (再試行)」参照)。本 plan はその繰越分を **新 moonshot plan として独立化**、Phase 0 inventory も親 inventory の delta に絞った専用版を起草。

**親 plan との関係**:
- 親 plan の `stein_achievability` を Phase B (parent) として既存資産扱い
- 本 plan の Phase A〜C で converse + Tendsto を 0 sorry 化し、`stein_lemma` (= Cover-Thomas Theorem 11.8.3 完全版) を本 plan の Definition of Done とする
- ファイル分割: 新ファイル `SteinConverse.lean` ではなく **`Stein.lean` への append** (achievability と statement / 仮定セットを共有、参照コスト最小)。判断: 親 plan のファイル構成を継続

**着手判定**: GO。inventory 確定で skeleton 直行可。

<!-- 本 plan はまだ起草段階。本体着手で発見があれば追記。 -->

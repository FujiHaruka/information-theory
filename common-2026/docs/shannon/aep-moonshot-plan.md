# AEP + 源符号化定理 ムーンショット計画 🌙🌙

<!--
雛形メモ:
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
- `rg "^- \[ \]"` で残タスク横断 grep、`rg "🔄"` でピボット箇所だけ拾える
-->

> 実態整合 (2026-05-20): DONE-HONEST-HYPS — 全 Phase 完了。Phase D weak converse =
> `source_coding_converse` (`InformationTheory/Shannon/AEP.lean:704`)、Phase E achievability =
> `source_coding_achievability` (AEP.lean:1138)、両側等号 `source_coding_theorem`
> (AEP.lean:1240)。AEP.lean 全体 0 sorry、仮定は i.i.d. 標準形 (`iIndepFun`/`IdentDistrib`/`hpos`) のみ。
>
> **Status (2026-05-10)**: 起草。シードカード [Seed 4](../moonshot-seeds.md#seed-4-aep--源符号化定理漸近-) を膨らませた本命 4〜6 週間ムーンショット。
> **撤退ライン**: Phase A〜C 完了 (= AEP 単体) で publish 価値あり。源符号化定理 (Phase D / E) はそこから separable に切り出せる。

## 進捗

- [x] Phase 0 — Mathlib + 既存 InformationTheory API インベントリ ✅ → [`aep-mathlib-inventory.md`](aep-mathlib-inventory.md)
- [x] Phase A — i.i.d. 列の formal definition + Pi 値 plumbing ✅ (= `jointRV` 定義 + 基本 `Measurable` のみ、Pi 構築は Phase B/C で実需要が出るまで保留 / 結局 B では不要、C.3 でのみ要)
- [x] Phase B — probability AEP (`P{|−(1/n) log P(X^n) − H(X)| ≥ ε} → 0`) ✅
- [x] Phase C — typical set `T_ε^n` ✅ (`measurableSet_typicalSet` ✅ / `typicalSet_prob_tendsto_one` ✅ / `typicalSet_card_le` ✅ — `[∀ x, P(x) > 0]` 仮定追加で完了)  ⬅ **撤退ラインはここ — Phase A〜C 完了 = AEP 単体 publish ライン到達**
- [x] Phase D — 源符号化定理 weak converse (`liminf_n (log M_n / n) ≥ entropy μ X`) ✅ (`source_coding_converse`, AEP.lean:704)
- [x] Phase E — achievability (rate > H で error → 0) ✅ (`source_coding_achievability`, AEP.lean:1138)

## ゴール / Approach

**最終到達点 (Phase D 本命)**: 源符号化定理 weak converse —
任意のブロック符号 `c_n / d_n` で `P{d_n(c_n(X^n)) ≠ X^n} → 0` ⟹ `liminf_n (log M_n / n) ≥ entropy μ X`。

**Approach の中核 (4 段)**:

1. **(a) i.i.d. predicate を Mathlib 既存に乗せる** ─ `Pairwise (IndepFun on Xs) ∧ ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ` の 2 仮定形をそのまま使い、自前 `IsIID` 構造体は導入しない (`aep-mathlib-inventory.md` 軸 1 結論)
2. **(b) `−(1/n) log P(X^n)` に強法則 `strong_law_ae_real` を適用** ─ `Y i := −Real.log ((μ.map (Xs 0)).real {Xs i ω})` を定義し、`IdentDistrib.comp` + `IndepFun.comp` で i.i.d. 性を lift
3. **(c) typical set を `Set` で定義し measurability を `measurableSet_lt` から引き出す** ─ size bound `|T_ε^n| ≤ 2^{n(H+ε)}` は `T_ε^n` の各点で `P(x^n) ≥ 2^{-n(H+ε)}` (定義から直接) + 確率の有限和上界
4. **(d) Phase D は `shannon_converse_single_shot` を block per-n 適用** ─ `M = M_n`, `Msg = X^n` (Phase A の Pi 値で構成, ただし `X^n` は uniform でないので Fano version で attack)

**撤退ライン**: Phase C 緑通過時点で **AEP 単体として publish OK**。Phase D で詰まる場合は次セッションに切り出す (源符号化定理 = AEP 機械の再演として独立価値)。Phase E (achievability) は Phase D 完了後の自然な次の step、Phase D 撤退時は同時 deferred。

**Approach 図**:

```
Phase 0  : Mathlib + InformationTheory API インベントリ              ← 1 ターン
           ──────────────────────────────────────────
Phase A  : i.i.d. 列の formal definition + Pi 値 joint law    ← 1〜1.5 週
           ──────────────────────────────────────────
Phase B  : probability AEP (強法則 + IdentDistrib lift)        ← 山場 (1)、1〜1.5 週
           ──────────────────────────────────────────
Phase C  : typical set T_ε^n (measurability + size + prob)    ← 0.5〜1 週
           ←───── 撤退ライン (AEP 単体 publish) ─────→
           ──────────────────────────────────────────
Phase D  : 源符号化定理 weak converse (liminf 形)              ← 山場 (2)、1〜1.5 週
           ──────────────────────────────────────────
Phase E  : achievability (rate > H で error → 0)              ← 0.5〜1 週
```

**ファイル構成 (Phase E 終了時想定)**:

```
InformationTheory/Shannon/
  AEP.lean             ← Phase A (i.i.d. plumbing) + Phase B (probability AEP)
  TypicalSet.lean      ← Phase C
  SourceCoding.lean    ← Phase D (converse) + Phase E (achievability)
```

撤退時 (Phase A〜C 完) は `InformationTheory/Shannon/AEP.lean` + `InformationTheory/Shannon/TypicalSet.lean` で close。

---

## Phase 0 — Mathlib + 既存 InformationTheory API インベントリ

### スコープ

`docs/shannon/aep-mathlib-inventory.md` を起草、6 軸 (LLN / IdentDistrib / log 可測性 / liminf / typical set measurability / Pi 構築) を裏取り。

### 進捗

- [x] サブ計画起草 (本ファイル + inventory file 同時、2026-05-10)
- [ ] Phase A 着手前の不確実性ランクが low になっている (= inventory 結論で skeleton が書ける状態)

### Done 条件

- 「強法則 `strong_law_ae_real` の verbatim 署名」が inventory に記録 → ✅ 起草段階で確定
- 「AEP / typical set / 源符号化定理は Mathlib 不在」を裏取り → ✅ `rg` 0 件確認
- Phase A skeleton (`InformationTheory/Shannon/AEP.lean` の sorry-driven 出だし) が書ける状態 → 本 plan 起草時点で **GO**

### 工数感

1 ターン (10〜15 分)。本起草で完。

---

## Phase A — i.i.d. 列の formal definition + Pi 値 plumbing 📋

### スコープ

```lean
namespace InformationTheory.Shannon

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                    [MeasurableSpace α] [MeasurableSingletonClass α]

/-- For convenience: the joint random variable `X^n : Ω → (Fin n → α)`. -/
def jointRV (Xs : ℕ → Ω → α) (n : ℕ) : Ω → (Fin n → α) :=
  fun ω i => Xs i ω

/-- The joint law of an i.i.d. block equals the product of marginals.
Used to convert `μ.map (jointRV Xs n)` into `Measure.pi`. -/
theorem map_jointRV_eq_pi
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Xs))
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (n : ℕ) :
    μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => μ.map (Xs 0))

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(A.1) `jointRV` 定義** + 基本 Measurable 性 (`Measurable.pi` で `hXs` から組む)
- [ ] **(A.2) `iIndepFun (fun i (ω : Ω) => Xs i ω)` の `Pairwise IndepFun` 同値 lift** ─ Mathlib に既存補題があれば呼ぶ、無ければ自前 (`InformationTheory/Shannon/Han.lean` 周辺の `IndepFun` 利用前例があるか確認)
- [ ] **(A.3) `map_jointRV_eq_pi` 本体** ─ `iIndepFun_iff_map_fun_eq_infinitePi_map` (`Mathlib/Probability/Independence/InfinitePi.lean:79`) を経由するか、`IdentDistrib.pi` (`Mathlib/Probability/IdentDistribIndep.lean:57`) + finite Pi reshape のいずれか。**最大の plumbing 不確実性** (40〜80 行見積もり)
- [ ] **(A.4) `(Fin n → α)` の `Fintype` / `MeasurableSpace` / `MeasurableSingletonClass` instance**: 自動発火確認 (Han Phase D 前例より GO 見込み)
- [ ] **(A.5) `InformationTheory.lean` に `import InformationTheory.Shannon.AEP` 追記**

### Done 条件

- 上記 5 項目が `lake env lean InformationTheory/Shannon/AEP.lean` で silent
- skeleton-driven で `jointRV` 定義 → `map_jointRV_eq_pi` の sorry を割る順序

### 工数感

1〜1.5 週。**最大リスク**: (A.3) `iIndepFun ↔ Pairwise IndepFun` + `iIndepFun → Measure.pi 形` の 2 段経由がスムーズに行くか。`IdentDistrib.pi` と `iIndepFun_iff_map_fun_eq_infinitePi_map` のどちらが効くかは着手時の `Fin n` ↔ `Countable ι` 整合で決まる。

### 撤退ライン (Phase A 内)

- (A.3) の plumbing で 5〜7 日溶ける場合 → `map_jointRV_eq_pi` を **`Fin 2` (= 単発 i.i.d. ペア) で限定版**にして Phase B に進み、一般 `n` への拡張は Phase B 完了後に再開

---

## Phase B — probability AEP 📋

### スコープ

```lean
namespace InformationTheory.Shannon

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                    [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Per-symbol log-likelihood: `−log P(Xs i ω)`. The Cesàro mean of this sequence
is the empirical entropy estimator. -/
noncomputable def logLikelihood
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (i : ℕ) : Ω → ℝ :=
  fun ω => -Real.log ((μ.map (Xs 0)).real {Xs i ω})

/-- Probability AEP (Asymptotic Equipartition Property):
`(1/n) ∑_i logLikelihood μ Xs i ω` converges in probability (and a.s.) to `entropy μ (Xs 0)`. -/
theorem aep_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Xs))
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
      Filter.atTop
      (𝓝 (entropy μ (Xs 0)))

theorem aep_inProbability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Xs))
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | ε ≤ |((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
                                  - entropy μ (Xs 0)|})
      Filter.atTop
      (𝓝 0)

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(B.1) `logLikelihood` の `Integrable`** ─ `α : Fintype` のもとで `(μ.map (Xs 0)).real {x}` は有限個の値、`Y 0 ω = −log ((μ.map (Xs 0)).real {Xs 0 ω})` は有界可測 (サポート上では log 値が有限、サポート外は `μ` で測度 0)。**支持外の単点 `(μ.map (Xs 0)).real {x} = 0` で `−log 0 = +∞` になる扱いが詰まりポイント候補**。Phase B の plumbing 山場 1。50〜100 行
- [ ] **(B.2) `μ[logLikelihood μ Xs 0] = entropy μ (Xs 0)`** ─ 期待値計算。`∫ ω, −log P(Xs 0 ω) ∂μ = ∑ x : α, (μ.map (Xs 0)).real {x} · (−log ((μ.map (Xs 0)).real {x})) = ∑ x, negMulLog ((μ.map (Xs 0)).real {x}) = entropy μ (Xs 0)`。`integral_finset_sum` 系 + `(μ.map (Xs 0)).real {x} = 0` 点の handling。30〜60 行
- [ ] **(B.3) `IdentDistrib (logLikelihood μ Xs i) (logLikelihood μ Xs 0)`** ─ `IdentDistrib.comp` を `Xs i ↦ Xs 0` の同分布から、`u : α → ℝ := fun x => −log ((μ.map (Xs 0)).real {x})` で lift。`u` の measurability は `α : Fintype` から自動 (有限関数)。20〜30 行
- [ ] **(B.4) `Pairwise (IndepFun on logLikelihood μ Xs)`** ─ `IndepFun.comp` を `Xs i, Xs j` の独立性から、`u` で lift。20〜30 行
- [ ] **(B.5) `aep_ae` 主定理** ─ `strong_law_ae_real` を `Y i := logLikelihood μ Xs i` で適用、結論を `∀ᵐ ω, Tendsto … (𝓝 μ[Y 0])` から `μ[Y 0] = entropy μ (Xs 0)` (B.2) で書き換え。1 段適用 + rewrite。15〜20 行
- [ ] **(B.6) `aep_inProbability`** ─ `tendstoInMeasure_of_tendsto_ae` (`Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:223`) で a.s. → 確率収束に lift、`TendstoInMeasure` の定義展開で `μ {ω | ε ≤ |...|} → 0` の形に整理。30〜50 行

### Done 条件

- 上記 6 項目が silent
- `aep_inProbability` が「教科書 AEP の標準形」(Cover-Thomas Theorem 3.1.1) と一致
- proof-log + metrics 取得済み (`docs/proof-logs/proof-log-aep.md`, `docs/metrics/aep.{manifest,metrics}.{json,md}`)

### 工数感

1〜1.5 週。**最大リスク**: (B.1) サポート外点 `(μ.map (Xs 0)).real {x} = 0` の handling。Mathlib `Real.log 0 = 0` (convention) を使えるなら積分可能性は直接従うが、entropy 定義側 `negMulLog 0 = 0` との整合 + 確率 0 点の除外が plumbing-heavy になる可能性あり。**事前撤退ライン**: B.1 で 4〜5 日溶けたら `[∀ x, (μ.map (Xs 0)).real {x} > 0]` を追加仮定して支持全体仮定で閉じる (Cover-Thomas 教科書もこの仮定で書くことが多い)。

### 撤退ライン (Phase B 内)

- (B.1) サポート外点の handling で 5〜7 日溶ける → `[∀ x : α, (μ.map (Xs 0)).real {x} > 0]` 仮定追加で閉じる、AEP の statement に「support 全体」仮定を入れる
- (B.5) で `strong_law_ae_real` の引数 `IdentDistrib (X i) (X 0)` の `μ μ` 同測度形が `logLikelihood` で integrable な形に乗らない → `strong_law_ae` (Banach 値) に切り替え (E = ℝ で同じ結論)

---

## Phase C — typical set `T_ε^n` 📋

### スコープ

```lean
namespace InformationTheory.Shannon

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                    [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The typical set: blocks `x : Fin n → α` whose empirical entropy is within `ε`
of the true entropy. -/
noncomputable def typicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) :
    Set (Fin n → α) :=
  { x | |(-(1 / (n : ℝ))) * (∑ i : Fin n, Real.log ((μ.map (Xs 0)).real {x i}))
          - entropy μ (Xs 0)| < ε }

theorem measurableSet_typicalSet
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) :
    MeasurableSet (typicalSet μ Xs n ε)

/-- Size bound: `|T_ε^n| ≤ 2^{n(H(X) + ε)}`. -/
theorem typicalSet_card_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (typicalSet μ Xs n ε).toFinset.card ≤
      Real.exp ((n : ℝ) * (entropy μ (Xs 0) + ε))

/-- Typicality probability: `P(X^n ∈ T_ε^n) → 1` as `n → ∞`. -/
theorem typicalSet_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Xs))
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε})
      Filter.atTop
      (𝓝 1)

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(C.1) `typicalSet` 定義** + 基本性質 (`x ∈ typicalSet ↔ ...`)
- [ ] **(C.2) `measurableSet_typicalSet`** ─ `measurableSet_lt` (`Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean:245`) を 2 回 (左右の不等式) + `MeasurableSet.inter`。20〜30 行
- [ ] **(C.3) `typicalSet_card_le`** ─ `x ∈ T_ε^n ⟹ Π_i P(x i) ≥ 2^{-n(H+ε)}` (定義から直接) + `∑_{x ∈ T_ε^n} Π_i P(x i) ≤ 1` (確率全体)。Real.exp / Real.log の往復で 50〜80 行
- [ ] **(C.4) `typicalSet_prob_tendsto_one`** ─ `μ {ω | jointRV Xs n ω ∈ T_ε^n}` を `aep_inProbability` (Phase B) の事象の **補集合の余事象**として書き直す。Phase A の `map_jointRV_eq_pi` で `μ.map (jointRV Xs n) {x | ...} = ...` に翻訳、Phase B `aep_inProbability` を直接適用。20〜40 行

### Done 条件

- 上記 4 項目が silent
- proof-log + metrics 取得済み

### 工数感

0.5〜1 週。**Phase B が片付けば組み合わせ + Pi 値 reshape のみ**。最大リスクは (C.4) で `jointRV Xs n` の像 `μ.map (jointRV Xs n)` 上の事象を Phase B `μ {ω | ...}` 上の事象に翻訳する `map_jointRV_eq_pi` の使い方。

### 撤退ライン (Phase C 内)

- (C.3) で `Real.exp / Real.log` の往復が plumbing-heavy → `2^{n(H+ε)}` の代わりに **`Real.exp (n · (H + ε))` のまま**で statement を書く (教科書も実は `2^x` ではなく `e^x` で書ける)、Real.exp で閉じる

### **★★★ Phase A〜C 完了 = AEP 単体 publish ライン ★★★**

ここで `InformationTheory/Shannon/AEP.lean` + `InformationTheory/Shannon/TypicalSet.lean` が立ち、教科書 AEP (Cover-Thomas Theorem 3.1.1〜3.1.2) の **standard 3 主定理** が形式化された状態。**Phase D 不達でもムーンショット成立。** proof-log + metrics 取得 + 別 plan に Phase D 切り出しの判断はここで実施。

---

## Phase D — 源符号化定理 weak converse 📋 (撤退時 deferred)

### スコープ

```lean
namespace InformationTheory.Shannon

/-- Source coding theorem, weak converse:
For any block code `(c_n, d_n)` with `M_n` codewords,
if the error probability vanishes then the rate is at least the entropy. -/
theorem source_coding_converse
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Xs))
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (M : ℕ → ℕ) (hM : ∀ n, 1 ≤ M n)
    (c : ∀ n, (Fin n → α) → Fin (M n))
    (d : ∀ n, Fin (M n) → (Fin n → α))
    (hc : ∀ n, Measurable (c n)) (hd : ∀ n, Measurable (d n))
    (hPe : Tendsto
      (fun n => μ {ω | d n (c n (jointRV Xs n ω)) ≠ jointRV Xs n ω})
      Filter.atTop (𝓝 0)) :
    entropy μ (Xs 0) ≤
      Filter.liminf (fun n : ℕ => Real.log (M n) / n) Filter.atTop

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(D.1) Block per-n に `shannon_converse_single_shot` を適用**
  - `M := M n`、`Msg := jointRV Xs n` (= `X^n : Ω → (Fin n → α)`)
  - `Yo := c n ∘ jointRV Xs n` (= channel output に相当、ここでは encoded message)
  - `decoder := d n`
  - **問題**: `Msg` が **uniform でない** ─ Phase D の最大の plumbing 課題。`shannon_converse_single_shot` は uniform 仮定 `μ.map Msg = (Fintype.card M)⁻¹ • Measure.count` に依存、`X^n` の分布は `(μ.map (Xs 0))^⊗ⁿ` で uniform でない
- [ ] **(D.2) Fano 直接適用版を別ルートで構築** ─ `shannon_converse_single_shot` の証明骨格 (Fano + DPI + Bridge) を **uniform 不要で再演**:
  - Fano: `H(X^n | d ∘ c ∘ X^n) ≤ h(Pe_n) + Pe_n · log (|α|^n - 1)` (これは `X` Fintype + Fano measure 版で OK)
  - DPI: `I(X^n; c(X^n)) ≤ I(c(X^n); c(X^n)) ≤ log M_n` (encoder 出力は `M_n` 値だから entropy ≤ log M_n)
  - Bridge: `H(X^n) = I(X^n; c(X^n)) + H(X^n | c(X^n))` ≤ `log M_n + h(Pe_n) + Pe_n · n · log |α|`
  - **整理**: `n · H(X) = H(X^n) ≤ log M_n + 1 + Pe_n · n · log |α|` から `H(X) ≤ log M_n / n + (1 + Pe_n · n · log |α|) / n`
  - `Pe_n → 0` + `log |α|` 有限 + `1/n → 0` で `liminf (log M_n / n) ≥ H(X)`
  - **新規**: `H(X^n) = n · H(X)` (i.i.d. の entropy additivity) ─ Phase A の `map_jointRV_eq_pi` から導出、20〜40 行
- [ ] **(D.3) `Tendsto → liminf`**: `Pe_n → 0` から `liminf (log M_n / n) ≥ H(X)` への `liminf_le_iff` 系の rewrite。`Filter.liminf` API を直接使う。30〜50 行

### Done 条件

- 上記 3 項目が silent
- proof-log + metrics 取得済み

### 工数感

1〜1.5 週。**最大リスク**: (D.2) `shannon_converse_single_shot` を直接呼ぶか、それとも証明骨格を再演するかの判断 + 証明骨格再演時の plumbing 量。`X^n` の uniform 化 (任意分布上の Fano + Bridge 直接適用) が思ったより重ければ撤退ラインに到達。

### 撤退ライン (Phase D 内)

- **撤退ライン本命** (Phase D 全体): D.2 で 5〜7 日溶けて骨格再演が plumbing-heavy → **本 plan は Phase A〜C で close**、源符号化定理 converse を別 plan `docs/shannon/source-coding-converse-moonshot-plan.md` に切り出し
- D.3 の `Filter.liminf` rewrite で詰まる → `liminf` を `lim sup of (≥)` 形に書き換えて Mathlib API を回避、または `Filter.liminf_le_of_le` 系を 2〜3 段組み合わせ

---

## Phase E — achievability (rate > H で error → 0) 📋 (撤退時 deferred)

### スコープ

```lean
namespace InformationTheory.Shannon

/-- Source coding theorem, achievability:
For any rate `R > H(X)`, there exists a block code with rate `R` and vanishing error. -/
theorem source_coding_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Xs))
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {R : ℝ} (hR : entropy μ (Xs 0) < R) :
    ∃ M : ℕ → ℕ, ∃ c : ∀ n, (Fin n → α) → Fin (M n),
       ∃ d : ∀ n, Fin (M n) → (Fin n → α),
      Tendsto (fun n => Real.log (M n) / n) Filter.atTop (𝓝 R) ∧
      Tendsto
        (fun n => μ {ω | d n (c n (jointRV Xs n ω)) ≠ jointRV Xs n ω})
        Filter.atTop (𝓝 0)

end InformationTheory.Shannon
```

### 鍵となる作業

- [ ] **(E.1) `M_n := ⌈Real.exp (n · R)⌉` 構成** + `c_n` を typical set 上の bijection で構成、外側は任意
- [ ] **(E.2) error 評価**: `P{X^n ∉ T_ε^n} → 0` (Phase C `typicalSet_prob_tendsto_one`) で error → 0
- [ ] **(E.3) rate 評価**: `log M_n / n → R` (`⌈⌉` の rounding error は `1/n → 0` で消える)

### 工数感

0.5〜1 週。Phase A〜D の素材を組み合わせるだけ、新規 plumbing は最小限。

---

## 失敗判定 / 撤退ライン (全体)

| 撤退ポイント | 判定基準 | アクション |
|---|---|---|
| Phase 0 で AEP / typical set / 源符号化定理が Mathlib にあった | 0 件確認済み (本 inventory) | 不該当 |
| Phase A の `map_jointRV_eq_pi` で 5〜7 日溶ける | (A.3) 進捗 0、Mathlib 既存補題が効かない | 単発 i.i.d. ペア限定で Phase B に進む、後で再開 |
| Phase B の `Integrable` で 4〜5 日溶ける | サポート外点 handling が plumbing-heavy | `[∀ x, (μ.map (Xs 0)).real {x} > 0]` 追加仮定で閉じる |
| **Phase C 完了 (= AEP 単体)** | 3 主定理 silent | **★ 撤退ライン: Phase D は次セッション ★** ─ 別 plan に切り出し、本 plan は close |
| Phase D の D.2 (証明骨格再演) で 5〜7 日溶ける | uniform 不要 Fano + Bridge の plumbing 量超過 | 別 plan に切り出し、Phase E も同時 deferred |
| Phase D の D.3 (`liminf` rewrite) で詰まる | Mathlib `Filter.liminf` API の不足 | 自前 `liminf_le_of_eventual` 系を 1〜2 本書く、それでもダメなら `lim` 形 statement に弱体化 |

どのケースも proof-log に **正直に**記録。Mathlib の薄い箇所を可視化したという結果自体がデモのデータポイント。

---

## 工数見積もり総括

| 経路 | 工数 | 行数 | リスク |
|---|---|---|---|
| Phase A〜C (AEP 単体 publish) | **2.5〜4 週** | **400〜700 行** | **中** (Phase A.3 の Pi reshape + Phase B.1 の Integrable handling) |
| Phase A〜E (源符号化定理本命まで) | 4〜6 週 | 800〜1500 行 | **高** (シード通り) |
| Phase D 単独 (AEP 後の追加分) | 1〜1.5 週 | 300〜500 行 | 中 (`shannon_converse_single_shot` 流用度次第) |
| Phase E 単独 (Phase D 後の追加分) | 0.5〜1 週 | 100〜300 行 | 低 (組み合わせのみ) |

撤退時 (Phase A〜C) でも **シード「800〜1500 行 / 高リスク」の半分弱**で AEP 単体が立つので、本 plan は **撤退時にも価値が残る**設計。

---

## 当面の next step

1. ✅ **Phase 0 (本 plan + inventory 起草)** — 完 (2026-05-10)
2. **Phase A skeleton** — `InformationTheory/Shannon/AEP.lean` を sorry-driven で書き始め、`jointRV` + `map_jointRV_eq_pi` の sorry を割る ← **次これ**
3. **Phase A 完で Phase B 着手判定** — `map_jointRV_eq_pi` が silent なら Phase B (probability AEP)
4. **Phase B 完で Phase C 着手判定** — Phase B が plumbing 山場 1 なので、ここを越えれば撤退ラインまでは見える
5. **Phase C 完 = 撤退ライン到達**: proof-log + metrics 取得、Phase D を別 plan に切り出すか継続するかをここで判断

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-10 — 第 1 セッション

**Phase A の小型化**: 計画上の `map_jointRV_eq_pi` (有限 Pi ↔ μ.map jointRV = Measure.pi 等式) は **Phase B では不要** (`strong_law_ae_real` は Pi 形ではなく `Y i := −log P(Xs i ω)` を直接受ける) と判断。Phase A は `jointRV` 定義 + 基本 `measurable_jointRV` のみに圧縮し、Pi 構築は Phase C.3 で実際に必要になったときまで保留。結果、**Phase A は半日相当で完了**、Phase B に直行。

**Phase B 主役は `pmfLog : α → ℝ` 経由**: `logLikelihood μ Xs i ω = pmfLog μ Xs (Xs i ω)` と `pmfLog x := −log ((μ.map (Xs 0)).real {x})` で書き、`α : Fintype` の `Measurable.of_finite` で `pmfLog` の measurability、`Integrable.of_finite` で `pmfLog` の `(μ.map (Xs i))` 上 integrable、`Integrable.comp_measurable` で `logLikelihood i` の `μ` 上 integrable、`integral_map` + `integral_fintype` で期待値 = entropy、`IdentDistrib.comp` / `IndepFun.comp` で i.i.d. 性 lift、`strong_law_ae_real` で a.s. 収束、`tendstoInMeasure_of_tendsto_ae` + `tendstoInMeasure_iff_dist` で確率収束。**plumbing は当初予測 50〜100 行 → 実際 70 行で完了**、サポート外点 `P(x) = 0` の handling は **`Real.log 0 = 0` 規約と `pmfLog x = 0` で素通り** (期待値 = entropy で `negMulLog 0 = 0` も同じ規約)。事前撤退路線 (`[∀ x, μ.map (Xs 0) {x} > 0]` 仮定追加) は不要。

**Phase B の `Pairwise (· ⟂ᵢ[μ] ·) on Xs` notation で parsing 詰まり**: `((· ⟂ᵢ[μ] ·) on Xs)` の anonymous lambda + `Function.onFun` 組み合わせが Lean 4 の elaborator で `⟂ᵢ[μ]` を `Prop` で解決して `on` を関数として要求 → mismatch。`Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j` の明示形に統一。Mathlib 内で `((· ⟂ᵢ[μ] ·) on Xs)` 表記が通っているのは StrongLaw.lean 内部の `variable` scope での special elaboration によると推測。ただし `strong_law_ae_real` への引数渡しは elaborator が unify するので問題なし。

**Phase C.3 撤退**: `typicalSet_card_le` (size bound `|T| ≤ exp(n(H+ε))`) は本セッション撤退。理由: 証明には (a) `pmfLog` の sum を `log (∏ P(x i))` に展開 (`Real.log_prod` + `P > 0` per-i)、(b) `∑_{x : Fin n → α} ∏ P(x i) = 1` (`Finset.prod_sum` の dual + `IsProbabilityMeasure (μ.map (Xs 0))` で `∑ P = 1`)、(c) `Real.exp` への往復、の 3 段が必要で見積もり 80〜120 行。**サポート外点 (`P(x) = 0`) の handling** が log_prod の `≠ 0` 仮定と衝突するため、`[∀ x, μ.map (Xs 0) {x} > 0]` (= サポート全体) 仮定追加で plumbing を軽くするのが筋。本セッションの「Phase A〜C 緑通過 = 完了」ライン到達済み (Phase A + Phase B + Phase C のうち 2/3 = `measurableSet_typicalSet` / `typicalSet_prob_tendsto_one` 完了) なので、C.3 は次セッションに分離。

**Phase D / E**: 当初計画通り次セッション以降。本セッションのスコープ外。

### 2026-05-11 — 第 2 セッション

**Phase C.3 完了 (option A 採用)**: `typicalSet_card_le` の `sorry` を `[∀ x, (μ.map (Xs 0)).real {x} > 0]` (= `hpos` 仮定) 追加で埋めた。約 90 行追加、`lake env lean` silent / `lake build` 緑通過。第 1 セッションが見積もった撤退ライン (option A +30〜50 行) より plumbing がやや多かったが、戦略は計画通り。

**`Real.log_prod` を回避し `Real.exp_sum` で進めたのが効いた**: 教科書経路の `−log P^n(x) = −∑ log P(x_i)` を `log` 側で展開する代わりに、`exp(−pmfLog x_i) = P x_i` の per-point 等式 (`Real.exp_log (hpos x)`) と `Real.exp_sum : exp(∑ f_i) = ∏ exp(f_i)` で `∏ P(x_i) = exp(−∑ pmfLog x_i)` を組み立てた。結果、`Real.log_prod` の `≠ 0` 仮定 + サポート外点 `Real.log 0 = 0` 規約との往復が不要、`hpos` から `Real.exp_log` を 1 回呼ぶだけで済んだ。教訓: **「`log` の和を展開する」より「`exp` の積を展開する」方が、log 0 = 0 規約周りの plumbing を回避しやすい**。

**追加仮定なし路線が破綻した理由**: 第 1 セッションの所感「Phase B では `Real.log 0 = 0` で素通りだったので C.3 も追加仮定なしで」は **C.3 では破綻**。理由: Phase B は **期待値 (積分) 計算** で `negMulLog 0 = 0 · 0 = 0` がサポート外点を自動で 0 寄与にするが、Phase C.3 は **card の下界** (= 各点で量を持ち上げる方向) で、サポート外点 `x ∈ T` に対して下界量 `∏ P(x_i) ≥ exp(−n(H+ε))` が `0 ≥ exp(...)` で破綻する。具体的に: $f(x) = \exp(-\sum \text{pmfLog}\ x_i)$ をサポート外点込みで定義しても、$\sum_x f(x) = (1 + |\{x:P(x)=0\}|)^n$ となり $\neq 1$ で和の上界が `exp` の積構造で閉じない。card_le に必要な「下界量 × card ≤ 1」が成立しない。教訓: **Mathlib `Real.log 0 = 0` 規約は積分計算 (寄与 0 で済む) では素通りだが、card 上界 (寄与の正の下界が必要) では追加仮定で潰すのが筋**。


# Shannon-Hartley operational capacity closure ムーンショット計画 🌙

**Status**: planned (2026-07-14) 📋 — operational capacity を faithful かつ非循環に def 化し、
`contAwgn_eq_shannonHartley` を genuine に攻略（証明まで）。真の壁核は単一 `wall:nyquist-2w-dof`
（prolate-DOF、converse 側限定）に閉じ込める。

> **Parent**: [`../textbook-roadmap.md`](../textbook-roadmap.md) §Ch.9 Shannon-Hartley（Ch.9.6）
> **関連**: [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md)
> （sampling theorem = CLOSED、Phase 3/4 の信号↔サンプル橋）/
> [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)（per-sample coding theorem =
> `awgn_achievability` / `awgn_converse`、Phase 3/4 の per-sample 資産）
> **Facts ledger**: `docs/shannon/shannon-facts.md`（あれば。machine 裏付けは code の `#print axioms` を SoT とし prose にキャッシュしない）

## 進捗

- [ ] Phase 0 — Mathlib + InformationTheory API 在庫 📋 → `docs/shannon/shannon-hartley-operational-inventory.md`（mathlib-inventory dispatch 予定）
- [ ] Phase 1 — operational infra（`IsBandlimited` / 連続時間 code / 雑音測度 / `contAwgnOperationalCapacity`）📋 **[mainline]**
- [ ] Phase 2 — prolate-DOF スペクトル理論（`timeBandLimitingOp` + 固有値集中）📋 **[stretch / 壁核]**
- [ ] Phase 3 — achievability（`contAwgn ≥ shannonHartley`）📋 **[mainline-adjacent、壁非依存の公算]**
- [ ] Phase 4 — converse（`contAwgn ≤ shannonHartley`、Phase 2 消費）📋 **[stretch]**
- [ ] Phase 5 — wire（`contAwgn_eq_shannonHartley` 組立 + `IsTwoWDegreesOfFreedom` 除去）📋 **[mainline = 5-min / stretch = 5-full]**

## ゴール / Approach

### Goal（最終達成状態）

`InformationTheory/Shannon/ShannonHartley.lean` の load-bearing free-`C` predicate
`IsTwoWDegreesOfFreedom W N₀ P C := C = 2·W·perSampleAwgnCapacity W N₀ P`
（`@audit:retract-candidate(load-bearing-predicate)`）を除去し、以下 2 段で honest 化 → closure:

1. **operational capacity を faithful・非循環に def**:
   `contAwgnOperationalCapacity W N₀ P : ℝ`（連続時間帯域制限 AWGN チャネルの達成可能 rate 上限、
   毎秒レート `limsup (log M(T))/T`）。
2. **`contAwgn_eq_shannonHartley : contAwgnOperationalCapacity W N₀ P = bandlimitedAwgnCapacity W N₀ P`**
   （= `W·log(1 + P/(N₀·W))`）を genuine に証明。既存 `twoW_perSample_eq_shannonHartley`（代数 leg、
   sorryAx-free）+ `bandlimitedAwgnCapacity` / `perSampleAwgnCapacity` def を再利用。

honesty bar 不変（CLAUDE.md「検証の誠実性」）: genuine に建て、真に詰まる sub-wall のみ
honest `sorry + @residual(wall:<slug>)` で分解。**load-bearing hyp / 循環 def / `:True` slot は禁止**。

### Approach（解の全体形 = 戦略）

Shannon-Hartley の operational 版 = **サンドイッチ**:
`bandlimitedAwgnCapacity ≤ contAwgnOperationalCapacity`（achievability, Phase 3）
`∧ contAwgnOperationalCapacity ≤ bandlimitedAwgnCapacity`（converse, Phase 4）
→ `le_antisymm` で等号（Phase 5）。

戦略の要は **2W という次元定数を def に埋めず、証明の 2 方向から emerge させる**:

- **achievability（≥）は sampling theorem + per-sample coding で閉じる**: rate `2W` でサンプリング
  → per T 窓で `n ≈ 2WT` サンプル → `awgn_achievability`（既所有、genuine）で
  `≈ exp(T·W·log(1+SNR))` メッセージの codebook → `whittaker_shannon_bandlimited`（sampling、CLOSED）
  で連続信号に reconstruct。**この向きは prolate（Phase 2）を要さない公算が高い**（codebook は
  こちらが構成するので converse 次元カウント不要）。唯一の懸念 = sinc-tail による essential
  time-limiting の edge-effect（下記 feasibility unknown）。
- **converse（≤）は prolate-DOF 上界が本質**: 受信信号を上位 `≈2WT` 個の prolate 固有関数に射影
  → `awgn_converse`（既所有、genuine）+ 次元カウント。**ここだけが `wall:nyquist-2w-dof` を要する**
  （time-and-band limiting operator `P_W Q_T P_W` の固有値集中 = Landau-Pollak-Slepian、Mathlib 不在）。

したがって **真の壁は converse 側の単一核 `nyquist-2w-dof`（Phase 2 → Phase 4）に閉じ込められる**。
Phase 1 の周辺インフラ（帯域制限述語・連続時間 code・雑音測度・capacity def）と Phase 3 achievability
は壁でない（in-project 定義・証明可能）。

### mainline / stretch route（DAG 選択）

**mainline = 最短で honest tier-2 に到達**（load-bearing predicate 除去 + 単一 wall-sorry 化）:

> Phase 0 → Phase 1（`contAwgnOperationalCapacity` 非循環 def）→ Phase 5-min
> （`IsTwoWDegreesOfFreedom` 除去、`contAwgn_eq_shannonHartley` を body `sorry + @residual(wall:nyquist-2w-dof)`
> で publish、`shannon_hartley_formula` を genuine な等号結論に書換）。

これ **単独で honesty defect（free-`C` load-bearing predicate）が消え、単一 honest wall-sorry に還元**される。
prolate を建てずとも tier-2 に到達（Definition of Done: type-check done）。

**stretch = full closure**（wall-sorry を genuine に討伐）:

> Phase 3（achievability、壁非依存で genuine 化を狙う）+ Phase 2（prolate）→ Phase 4（converse）
> → Phase 5-full（サンドイッチ組立）。Phase 3 が壁非依存で閉じれば **`≥` 方向は genuine**、
> 残 `≤` 方向のみ `wall:nyquist-2w-dof` を担う中間状態を経る。

route 選択の指針: **まず mainline で honest 化（load-bearing predicate 即除去）**、次に stretch を
**Phase 3（achievability、壁非依存の公算・低リスク）→ Phase 2（壁核、最深）→ Phase 4** の順で攻める。
Phase 3 が先に閉じれば残壁が converse 単独に可視化され、Phase 2/4 の投資判断が明確になる。

---

## 設計制約 — 循環罠 #2 回避（独立節・非循環設計の受入基準）

proof-pivot-advisor 名指しの循環罠: **連続時間 code を「長さ `⌊2WT⌋` のサンプルベクトルに制限」して
定義してはならない**。それは converse の DOF 限界（Landau-Pollak-Slepian）を def に埋め込む循環
（= 連続容量をサンプル済有限次元容量として定義に等価化）で、還元定理が `rfl` 化し証明が空になる。

**非循環設計の受入基準**（各 def は下記を満たすこと。各 Phase の「循環チェック」欄で照合）:

1. **C1 — codeword 空間**: codeword は `[0,T]` 上の**任意の帯域制限 `[-W,W]` 信号**（essentially
   time-limited to `[0,T]`）を許す。固定長サンプルベクトル `Fin ⌊2WT⌋ → ℝ` への制限は**禁止**。
2. **C2 — capacity primitive**: `contAwgnOperationalCapacity := limsup (log M(T))/T` を primitive として
   定義。`M(T)` は「error prob → 0 で区別可能な最大メッセージ数」= operational 量で、**次元定数
   `2W`・`⌊2WT⌋` を一切含まない**。
3. **C3 — 2W の出所**: 定数 `2W`（および `⌊2WT⌋`）は Phase 1 の**どの def にも現れない**。
   achievability 証明（Phase 3、サンプリング rate 選択）と converse 証明（Phase 4、prolate 次元カウント）
   の**両側から emerge** させる。
4. **C4 — 雑音測度**: 雑音測度は関数空間（帯域制限 L²）上の Gaussian 測度として、または
   サンプル数 `n` を**自由 ℕ パラメータ**として（`n → ∞` の極限 / 観測方式上の sup）定義。
   `n = ⌊2WT⌋` に**定義段で固定してはならない**（固定は C1 違反の別形）。

**違反の兆候（tell）**: `contAwgn_eq_shannonHartley` の証明が `rfl` / `unfold` のみで済む、`M(T)` の def に
`Fin (⌊2WT⌋)` が出る、reduction 定理が per-sample capacity をそのまま返す。これらが出たら循環。

---

## Phase 0 — Mathlib + InformationTheory API 在庫 📋

**目的**: 各 Phase の feasibility を確定させる。特に Phase 2（prolate = 壁核）と Phase 1（雑音測度・
帯域制限）の Mathlib 資産有無を verbatim signature で確認。**mathlib-inventory へ dispatch**
（書込先 `docs/shannon/shannon-hartley-operational-inventory.md`、docs-only）。
proof-log: no（inventory doc が成果物）。

**在庫優先ターゲット top 5**（feasibility 直結順）:

1. **コンパクト自己共役作用素のスペクトル理論 + 固有値カウント**（Phase 2 crux）:
   `ContinuousLinearMap.IsSelfAdjoint` / compact operator（`IsCompactOperator` / `HilbertSchmidt`）/
   スペクトル定理（`ContinuousLinearMap.IsSelfAdjoint` の固有値分解、`LinearMap.IsSymmetric` 経由）/
   固有値列の存在 + `spectrum`。**固有値集中/カウントの asymptotic は壁公算が高い** — 何が既存で
   何が不在かを verbatim で。
2. **Gaussian 過程 / 白色雑音測度**（Phase 1 雑音）: `ProbabilityTheory.IsGaussianProcess` /
   `GaussianProjectiveFamily` / `gaussianReal` / `Measure.pi (gaussianReal 0 σ)` /
   projective family の Kolmogorov extension。関数空間 Gaussian 測度が組めるか（route α）、
   iid サンプル pushforward で足りるか（route β）を判定。
3. **FourierTransform + 帯域制限 support + L² isometry**（Phase 1 `IsBandlimited`）:
   `Real.fourierIntegral` / `𝓕` / `tsupport` / `MeasureTheory.Lp.fourierTransformₗᵢ`（Plancherel
   L² isometry）/ Paley-Wiener 系。任意 `W`（Hz）へのスケーリング規約
   （WhittakerShannon は正規化 `[-1/2,1/2]`、ShannonHartley は実 `W`）の橋。
4. **`limsup` / rate 機構**（Phase 1 capacity def）: `Filter.limsup` /
   `Filter.Tendsto ... atTop` / `sSup` over code family / `Nat.ceil (Real.exp ...)`。
   `limsup (fun T => Real.log (M T) / T)` の可読 def 形。
5. **既存 in-project 再利用面**（Phase 3/4 橋、signature は確認済 = 下記 §依存）:
   `AWGN.Basic.AwgnCode` / `awgn_achievability`（`AWGN/Achievability.lean`）/
   `awgn_converse`（`AWGN/Converse.lean:607`）/ `WhittakerShannon.whittaker_shannon_bandlimited` /
   `ShannonHartley.bandlimitedAwgnCapacity` / `perSampleAwgnCapacity` / `twoW_perSample_eq_shannonHartley`。

**受入基準**: 各ターゲットに structured per-lemma 出力（`file:line` + verbatim signature + `[...]`
型クラス前提 + 結論形、CLAUDE.md「Subagent Inventory」準拠）。特に Phase 2 の「固有値カウント asymptotic
が Mathlib 不在か」を loogle `Found 0` 裏取り + conclusion-shape 二段検索で確定。

---

## Phase 1 — operational infra 📋 **[mainline]**

**目的**: 帯域制限述語・連続時間 code・雑音測度・`contAwgnOperationalCapacity` を非循環に定義。
壁でない。proof-log: yes。概算 300–500 行。

**主要 def（signature スケッチ、型は要 inventory 確認 = ⟨?⟩）**:

```lean
/-- 帯域制限述語: 𝓕 f の台が [-W, W] に含まれる。W のスケーリング規約は要 inventory 確認。 -/
def IsBandlimited (f : ℝ → ℂ) (W : ℝ) : Prop := ∀ ξ : ℝ, W < |ξ| → 𝓕 f ξ = 0   -- ⟨? 規約⟩

/-- 連続時間 AWGN code: encoder は [0,T] essentially time-limited な帯域制限信号（C1）。 -/
structure ContAwgnCode (T W P : ℝ) (M : ℕ) where
  encoder : Fin M → (ℝ → ℂ)
  encoder_bandlimited : ∀ m, IsBandlimited (encoder m) W
  encoder_power : ∀ m, (∫ t in Set.Icc 0 T, ‖encoder m t‖ ^ 2) ≤ T * P   -- 平均電力 ≤ P
  decoder : ⟨受信信号空間 ?⟩ → Fin M
  decoder_meas : Measurable decoder

/-- 帯域制限白色雑音の測度。route α（関数空間 Gaussian）/ β（iid サンプル pushforward）は判断ログ軸。 -/
noncomputable def contBandlimitedNoise (T W N₀ : ℝ) : Measure ⟨受信信号空間 ?⟩ := ⟨? Phase 1 決定⟩

/-- error prob → 0 で区別可能な最大メッセージ数（operational primitive、C2: 2W を含まない）。 -/
noncomputable def contAwgnMaxMessages (T W N₀ P ε : ℝ) : ℕ :=
  sSup { M : ℕ | ∃ c : ContAwgnCode T W P M, ∀ m, (errorProb c m) ≤ ε }   -- ⟨errorProb 定義 ?⟩

/-- **operational capacity**（毎秒レート、C2 primitive）。 -/
noncomputable def contAwgnOperationalCapacity (W N₀ P : ℝ) : ℝ :=
  Filter.limsup (fun T : ℝ => Real.log (contAwgnMaxMessages T W N₀ P /- ε→0 の扱い ?-/) / T) Filter.atTop
```

**依存（DAG edge）**: Phase 0 → Phase 1。Phase 1 → Phase 3 / Phase 4 / Phase 5。
**循環チェック**: C1（`encoder : Fin M → (ℝ → ℂ)`、サンプルベクトルでない ✓）/ C2（`contAwgnMaxMessages`
に `2W`・`Fin ⌊2WT⌋` 不在 ✓ を実装時照合）/ C4（`contBandlimitedNoise` が `n = ⌊2WT⌋` 固定でない ✓）。
**受入基準**:
- **proof-done 条件**: 全 def が type-check、`IsBandlimited` の基本補題（scaling / linearity）が genuine、
  雑音測度が genuine に構成（route α or β）。
- **honest-sorry 分解条件**: 雑音測度の存在証明が `IsGaussianProcess` 不足で詰まる場合、**def を
  Mathlib-shape-driven で書換**（audit-tags「sorry を書けない順序」§1）— 測度の存在を別 `theorem` に
  切出し body `sorry`。この場合 **新規 proposed wall `cont-awgn-noise-measure`**（下記 sub-wall map、
  register 追加は promote 判断まで留保）。**load-bearing hyp で抱えるのは禁止**。
**feasibility unknown（inventory 待ち）**: (a) 受信信号空間の型（帯域制限 `Lp ℂ 2` か、サンプル列 `ℕ → ℝ`
か）、(b) 雑音測度 route α/β の可否（`IsGaussianProcess` の充足度）、(c) `ε → 0` を capacity def にどう
織り込むか（inf over ε / 二重極限）。
**retreat line**: def 自体に sorry は書けない（audit-tags §「sorry を書けない順序」）→ 詰まったら
雑音測度存在を theorem 化し body `sorry + @residual(wall:cont-awgn-noise-measure)`（proposed）。
capacity def / code structure は sorry 無しで組める前提。

---

## Phase 2 — prolate-DOF スペクトル理論 📋 **[stretch / 壁核・最深]**

**目的**: time-and-band limiting operator `P_W Q_T P_W`（`Q_T` = `[0,T]` 時間制限、`P_W` = `[-W,W]`
帯域制限射影）のコンパクト自己共役性 + prolate-spheroidal 固有値集中（>1/2 の固有値が `≈2WT + O(log WT)`
個 = Landau-Pollak-Slepian）。**真の sub-wall = `wall:nyquist-2w-dof`**。proof-log: yes。概算 800–1500 行。

**主要 theorem（signature スケッチ）**:

```lean
/-- time-and-band limiting operator P_W ∘ Q_T ∘ P_W（自己共役・コンパクト）。 -/
noncomputable def timeBandLimitingOp (T W : ℝ) :
    (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) := ⟨? P_W ∘ Q_T ∘ P_W⟩

theorem timeBandLimitingOp_isSelfAdjoint (T W : ℝ) :
    (timeBandLimitingOp T W).IsSelfAdjoint := ⟨genuine 目標⟩

theorem timeBandLimitingOp_isCompact (T W : ℝ) :
    IsCompactOperator (timeBandLimitingOp T W) := ⟨genuine 目標。Hilbert-Schmidt 経由が有力⟩

/-- prolate 固有値列（降順、スペクトル定理から）。 -/
noncomputable def prolateEigenvalues (T W : ℝ) : ℕ → ℝ := ⟨? spectrum⟩

/-- **壁核**: >1/2 の固有値カウント = ⌊2WT⌋ + O(log WT)（Landau-Pollak-Slepian）。 -/
theorem prolate_eigenvalue_count (T W : ℝ) (hT : 0 < T) (hW : 0 < W) :
    ⟨#{n | 1/2 < prolateEigenvalues T W n} と 2WT の集中不等式⟩ := by
  sorry   -- @residual(wall:nyquist-2w-dof)
```

**依存（DAG edge）**: Phase 0 → Phase 2。Phase 2 → Phase 4（converse、上位次元カウント）。
achievability（Phase 3）は **Phase 2 に依存しない公算**（下記）。
**循環チェック**: 本 Phase は def でなく作用素の解析。C3（`2WT` は固有値カウントの**結論**として現れ、
def の入力ではない ✓）。
**受入基準**:
- **proof-done 条件（stretch）**: 作用素定義 + 自己共役 + コンパクト性が genuine、固有値集中が genuine。
- **honest-sorry 分解条件（現実的着地）**: 作用素 + 自己共役 + コンパクト性は **genuine を目標**（Mathlib
  compact operator + spectral theorem の上に建設可能か Phase 0 で確定）。**固有値集中の asymptotic
  `prolate_eigenvalue_count` は最有力の genuine 壁** → body `sorry + @residual(wall:nyquist-2w-dof)`。
  load-bearing hyp / `*Hypothesis` predicate 化は禁止（audit-tags register の `nyquist-2w-dof` に集約）。
**feasibility unknown（inventory 待ち）**: (a) Mathlib のスペクトル定理が本作用素に適用できる形か
（`IsSelfAdjoint` + compact → 固有値分解）、(b) 固有値の**存在・降順列挙**が既存 API で取れるか、
(c) 集中不等式（Landau-Pollak-Slepian）の Mathlib 不在は確定的（loogle `Found 0`: prolate/Slepian、
2026-07-14）→ **self-build ~800-1500 行のスペクトル解析**、詰まれば honest sorry で分解し次 leg。
**retreat line**: `prolate_eigenvalue_count` を `sorry + @residual(wall:nyquist-2w-dof)`。
作用素の自己共役・コンパクト性が Mathlib 不足で詰まる場合も、その**個別補題**を sorry 化
（`@residual(wall:nyquist-2w-dof)` に集約、compound 化しない）。

---

## Phase 3 — achievability 📋 **[mainline-adjacent、壁非依存の公算]**

**目的**: `bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P`。
rate `2W` サンプリング → per-sample `awgn_achievability`（既所有 genuine）→ `whittaker_shannon_bandlimited`
（sampling、CLOSED）で連続信号 reconstruct。proof-log: yes。概算 300–600 行。

**主要 theorem（signature スケッチ）**:

```lean
theorem contAwgn_ge_shannonHartley (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P := ⟨sandwich の ≥ 方向⟩
```

**構成 leg**（既存資産再利用）:
- `awgn_achievability P _ N _ _ hR_pos hR hε` → per T 窓 `n = ⌊2WT⌋` サンプルで
  `M ≥ ⌈exp(n·(1/2)log(1+SNR'))⌉ = ⌈exp(T·W·log(1+SNR'))⌉` の `AwgnCode M n P'`。
- `whittaker_shannon_bandlimited`（信号 ↔ サンプル橋）で `AwgnCode` の encoder（`Fin n → ℝ`）を
  帯域制限連続信号 `ℝ → ℂ` に持ち上げ、`ContAwgnCode` を構成。
- 電力/雑音簿記: per-sample 電力 `P/(2W)` ↔ 連続電力 `P`（Parseval）、per-sample 雑音分散 `N₀/2` ↔
  白色雑音 PSD（Phase 1 雑音測度のサンプル表現）。
**依存（DAG edge）**: Phase 1 + WhittakerShannon（CLOSED）+ AWGN.awgn_achievability（genuine）→ Phase 3。
**Phase 2 には依存しない公算が高い**（codebook はこちらが構成 = converse 次元カウント不要）。
**循環チェック**: サンプリング rate `2W` は achievability 側の**構成選択**であり def の入力でない（C3 ✓）。
`M(T)` を `⌊2WT⌋` サンプルに制限するのではなく、その値以上のメッセージ数を**達成できる**と示すだけ（C1/C2 ✓）。
**受入基準**:
- **proof-done 条件**: `≥` を genuine 証明（`awgn_achievability` + `whittaker_shannon_bandlimited` +
  Parseval 電力橋 + 雑音サンプル iid Gaussian）。壁 sorry を含まず閉じられれば **`≥` 方向 genuine**。
- **honest-sorry 分解条件**: edge-effect（下記）で詰まる箇所のみ sorry。
**feasibility unknown（最大の懸念）**: **sinc-tail による essential time-limiting の edge-effect**。
Whittaker-Shannon reconstruction は全直線信号を返し、`[0,T]` への制限で sinc tail のエネルギー漏れが出る。
per-second rate `limsup (T→∞)` で edge が洗い流せる（guard interval 論法）か、**軽い prolate 下位カウント**
を要するかが分岐。前者なら壁非依存で genuine closure、後者なら `wall:nyquist-2w-dof` を一部共有。
Phase 0 / 実装で早期に判定。
**retreat line**: edge-effect が guard-interval で閉じない場合、その補題を
`sorry + @residual(wall:nyquist-2w-dof)`（converse 壁と同核・下位カウント側）。主要 leg
（`awgn_achievability` 呼出・reconstruction）は genuine の前提。

---

## Phase 4 — converse 📋 **[stretch]**

**目的**: `contAwgnOperationalCapacity W N₀ P ≤ bandlimitedAwgnCapacity W N₀ P`。
受信信号を上位 `≈2WT` prolate 固有関数（Phase 2）に射影 → `awgn_converse`（既所有 genuine）+ 次元カウント。
proof-log: yes。概算 400–700 行。

**主要 theorem（signature スケッチ）**:

```lean
theorem contAwgn_le_shannonHartley (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    contAwgnOperationalCapacity W N₀ P ≤ bandlimitedAwgnCapacity W N₀ P := ⟨sandwich の ≤ 方向⟩
```

**構成 leg**:
- Phase 2 `prolate_eigenvalue_count` で「有効次元 ≤ `⌊2WT⌋ + O(log WT)`」を得る（**壁核を消費**）。
- 上位固有関数への射影で受信信号を `≈2WT` 次元に還元 → per-letter `awgn_converse`
  （`Real.log M ≤ n·(1/2)log(1+P/N) + binEntropy(Pe) + Pe·log(M-1)`）を適用。
- `limsup (T→∞)` + Fano 項消滅（`Pe → 0`）で `≤ W·log(1+P/(N₀·W))`。
**依存（DAG edge）**: Phase 1 + Phase 2（`prolate_eigenvalue_count`）+ AWGN.awgn_converse（genuine）→ Phase 4。
**循環チェック**: **最重要**。C3 — `⌊2WT⌋` は Phase 2 固有値カウントの**結論**として converse に入り、
capacity def からは来ない ✓。受信信号を射影で次元還元するのは**証明ステップ**であり code def の制限でない
（C1 維持 ✓）。ここで「code をサンプルベクトルに制限」した瞬間に循環化する — 射影は受信側の解析、
codeword 空間は Phase 1 の任意帯域制限信号のまま。
**受入基準**:
- **proof-done 条件**: Phase 2 genuine 前提で `≤` を genuine 証明。
- **honest-sorry 分解条件**: Phase 2 の `prolate_eigenvalue_count` が sorry 状態なら、Phase 4 は
  それを transitive 継承し `contAwgn_le_shannonHartley` も `@residual(wall:nyquist-2w-dof)`
  （Phase 4 独自の新 sorry は作らず Phase 2 継承）。
**feasibility unknown（inventory 待ち）**: 射影後の受信分布が `awgn_converse` の要求形（`AwgnCode M n P`
+ per-letter Gaussian）に載るか。prolate 固有関数系での Parseval / 電力保存。
**retreat line**: Phase 2 継承の `@residual(wall:nyquist-2w-dof)`。射影 → `awgn_converse` 配線が
Mathlib 不足で詰まる個別補題は同 wall に集約。

---

## Phase 5 — wire 📋 **[mainline = 5-min / stretch = 5-full]**

**目的**: `IsTwoWDegreesOfFreedom` 除去 + `contAwgn_eq_shannonHartley` 組立 + `shannon_hartley_formula`
書換。proof-log: no（wiring + 代数再利用、小規模）。概算 50–120 行。

**5-min（mainline、Phase 3/4 前でも即実行可）**:

```lean
/-- operational capacity = Shannon-Hartley 閉形式。Phase 3/4 完成前は wall-sorry。 -/
theorem contAwgn_eq_shannonHartley (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    contAwgnOperationalCapacity W N₀ P = bandlimitedAwgnCapacity W N₀ P := by
  sorry   -- @residual(wall:nyquist-2w-dof)
```

- `IsTwoWDegreesOfFreedom`（free-`C` load-bearing predicate、`@audit:retract-candidate`）を**削除**。
- `shannon_hartley_formula` を書換: 結論を `contAwgnOperationalCapacity W N₀ P = bandlimitedAwgnCapacity W N₀ P`
  へ（自由 `C` + `h_two_w` を除去、`C := contAwgnOperationalCapacity W N₀ P` は def された operational 量で
  自由変数でない → **load-bearing predicate 消滅、honest tier-2 = 単一 wall-sorry**）。
- **ripple（mechanical 確認済）**: `IsTwoWDegreesOfFreedom` の consumer は `shannon_hartley_formula`
  **1 decl / 1 file のみ**（`scripts/dep_consumers.sh` = direct 1 decl、`rg` で ShannonHartley.lean 外の
  参照 0、NormalizedSinc.lean は docstring 言及のみ）。blast radius は ShannonHartley.lean 内に閉じる。
  `IsBandlimitedSamplingHypothesis` / `IsBandlimitedKernel`（残る positivity carrier）も同 file 内のみ。

**5-full（stretch、Phase 3 + Phase 4 完了後）**:

```lean
theorem contAwgn_eq_shannonHartley ... :=
  le_antisymm (contAwgn_le_shannonHartley ...) (contAwgn_ge_shannonHartley ...)
```

- Phase 3 `≥` + Phase 4 `≤` の `le_antisymm`。`twoW_perSample_eq_shannonHartley`（代数 leg、sorryAx-free）+
  `bandlimitedAwgnCapacity` / `perSampleAwgnCapacity` def を再利用。
- Phase 3 が genuine・Phase 4 が sorry の中間状態では、`contAwgn_eq_shannonHartley` は `≤` 経由で
  `@residual(wall:nyquist-2w-dof)` を継承（`≥` は genuine）。
**依存（DAG edge）**: Phase 1 → Phase 5-min（即）。Phase 3 + Phase 4 → Phase 5-full。
**循環チェック**: 書換後の `shannon_hartley_formula` が genuine 等号（`rfl` でない、Phase 3/4 の実証明 or
honest wall-sorry を経由）であることを確認。free-`C` predicate が消えていること。
**受入基準**:
- **5-min proof-done 条件（= mainline 到達）**: `contAwgn_eq_shannonHartley` が type-check（body wall-sorry）、
  `IsTwoWDegreesOfFreedom` 削除、`shannon_hartley_formula` が genuine 結論に書換、`#print axioms` で
  `sorryAx` が `nyquist-2w-dof` 由来のみ。独立 honesty audit（新 `@residual` 導入なので必須）で
  load-bearing 消滅 + `wall:nyquist-2w-dof` 分類正当を確認。
- **5-full proof-done 条件（= closure）**: `contAwgn_eq_shannonHartley` 0 sorry / 0 residual、`@audit:ok`。
**retreat line**: 5-min の `contAwgn_eq_shannonHartley` body `sorry + @residual(wall:nyquist-2w-dof)`。
これが mainline の honest 着地点（Definition of Done: type-check done）。

---

## Sub-wall map

| Phase | 生む見込みの residual | 位置づけ |
|---|---|---|
| Phase 1（雑音測度） | `wall:cont-awgn-noise-measure`（**proposed**、register 未追加） | brief は「雑音測度は壁でない」= in-project 定義可（proof-pivot-advisor + loogle 裏付け）。`IsGaussianProcess` で route α/β のいずれかが通る前提。**詰まった場合のみ** proposed wall として promote 判断（register 追加は後続）。**第一選択は genuine 構成** |
| Phase 2（prolate 固有値集中） | `wall:nyquist-2w-dof`（**最有力・確定的**） | 真の壁核。作用素定義 + 自己共役 + コンパクト性は genuine 目標、**固有値集中 asymptotic のみ**が genuine 壁（loogle `Found 0`: prolate/Slepian、self-build ~800-1500 行）。詰まれば `prolate_eigenvalue_count` を honest sorry で分解し次 leg |
| Phase 3（achievability edge-effect） | `wall:nyquist-2w-dof`（**一部共有の可能性**） | sinc-tail essential time-limiting が guard-interval で閉じれば**壁非依存で genuine**、閉じなければ下位カウント側で同核を一部共有。主要 leg（`awgn_achievability` + reconstruction）は genuine |
| Phase 4（converse） | `wall:nyquist-2w-dof`（**Phase 2 transitive 継承**） | Phase 2 の `prolate_eigenvalue_count` を継承。Phase 4 独自の新 sorry は作らない（射影 → `awgn_converse` 配線が詰まる箇所のみ同 wall 集約） |
| Phase 5-min | `wall:nyquist-2w-dof`（mainline 着地点） | `contAwgn_eq_shannonHartley` body の単一 honest wall-sorry。**これが load-bearing predicate 除去後の honest tier-2** |

**register 整合**: `nyquist-2w-dof` は `docs/audit/audit-tags.md` Wall name register に既存
（consumer が `IsTwoWDegreesOfFreedom` から `contAwgn_eq_shannonHartley` に移る旨を Phase 5 完了時に
register note へ反映 = mathlib-inventory / 実装 owner の担当、本 plan は prose に壁事実をキャッシュしない）。

各 node の前提: **genuine に詰まったら honest `sorry + @residual(wall:nyquist-2w-dof)` で分解し次 leg**。
load-bearing hyp / `*Hypothesis` predicate 化 / 循環 def / `:True` slot は全 Phase で禁止（CLAUDE.md）。

---

## 依存 DAG / ripple

```
Phase 0 (inventory) ──► Phase 1 (infra) ──┬─► Phase 3 (achievability, 壁非依存の公算) ─┐
                                          │                                          ├─► Phase 5-full
                    Phase 0 ─► Phase 2 (prolate/壁核) ─► Phase 4 (converse) ──────────┘
                                                                                      │
                    Phase 1 ──────────────────────────────────────────► Phase 5-min ─┘ (mainline 着地)
```

- **mainline path**: `0 → 1 → 5-min`（load-bearing predicate 除去 + 単一 wall-sorry、Definition of Done type-check）。
- **stretch path**: `0 → 1 → 3`（achievability genuine 化を先に）→ `2 → 4`（converse、壁核）→ `5-full`（closure）。
- **ripple（signature 変更）**: `IsTwoWDegreesOfFreedom` 削除の直接 consumer = `shannon_hartley_formula`
  1 decl（同 file）。ShannonHartley.lean 外の参照 0（`dep_consumers` + `rg` 確認済）。effort は Phase 5 に
  ~50–120 行で吸収。`InformationTheory.lean` の import は既登録（ShannonHartley / WhittakerShannon）。

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active な判断のみ残す（≤ 10 entry）。

1. **mainline = Phase 5-min（load-bearing predicate 即除去）を最優先**: full closure（prolate）を待たず
   `IsTwoWDegreesOfFreedom` free-`C` predicate を除去して honest tier-2（単一 wall-sorry）に到達する。
   proof-pivot-advisor 案の Phase 順（1→2→3→4→5）は stretch path、mainline は `0→1→5-min` の最短。
2. **stretch は Phase 3（achievability）を Phase 2（prolate）より先に**: achievability は
   `awgn_achievability` + `whittaker_shannon_bandlimited`（両 genuine/CLOSED）で**壁非依存に閉じる公算**
   （codebook 構成側 = converse 次元カウント不要）。先に閉じれば残壁が converse 単独に可視化され、
   Phase 2 の重投資判断が明確化。**唯一の懸念 = Phase 3 の sinc-tail edge-effect**（guard-interval で
   閉じるか要検証、feasibility unknown）。
3. **真の壁核は converse 側の `nyquist-2w-dof` 単一**: Phase 2（固有値集中）→ Phase 4（converse 上位
   カウント）に閉じ込める。Phase 1 雑音測度 / Phase 3 achievability は壁非依存を第一目標。
4. **雑音測度 route α（関数空間 Gaussian）vs β（iid サンプル pushforward）は Phase 1 の決定軸**（未確定）:
   Phase 0 inventory の `IsGaussianProcess` / `GaussianProjectiveFamily` 充足度で決める。route β は
   C4 違反（`n = ⌊2WT⌋` 固定）にならないよう **`n` を自由パラメータ**に保つこと。
5. **循環罠 #2 は設計制約節が SoT**: 各 Phase の「循環チェック」欄で C1–C4 を照合。特に Phase 4 の
   受信信号射影は「証明ステップであって code def の制限でない」を厳守（codeword 空間は Phase 1 の
   任意帯域制限信号のまま）。

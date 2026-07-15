# Shannon-Hartley operational capacity closure ムーンショット計画 🌙

**Status**: 🔄 **mainline OVERTURNED（2026-07-15、独立 honesty audit で機械確認、commit e711aa03）**。
2026-07-14 の tier-2 audit は覆り、既 publish 済 mainline `contAwgn_eq_shannonHartley` は現行 Phase 1 def の下で
**`P > 0` で FALSE-as-framed**（degenerate `IsBandlimited` + a.e.-class encoder 上の pointwise `sampledSignal`）。
コード側 SoT = `ShannonHartleyOperational.lean` の `@audit:defect(degenerate)`（`IsBandlimited`）/
`@audit:defect(false-statement)`（`contAwgn_eq_shannonHartley`、2026-07-14 stamp を OVERTURNED 明記）。
**新 mainline blocker = Phase 1-fix（def 再設計）**: Phase 1 def を faithful・非退化に建て直し
`contAwgn_eq_shannonHartley` を true-as-framed に復帰させ、honest な単一 wall-sorry
`@residual(wall:nyquist-2w-dof)` を回復する（**`nyquist-2w-dof` が genuine documented wall なのは
statement が true になった後に限る**）。stretch（Phase 3 achievability closure）は Phase 1-fix に gated。
honesty bar 不変（CLAUDE.md「検証の誠実性」）。

> **Parent**: [`../textbook-roadmap.md`](../textbook-roadmap.md) §Ch.9 Shannon-Hartley（Ch.9.6）
> **関連**: [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md)
> （sampling theorem = CLOSED、Phase 3/4 の信号↔サンプル橋）/
> [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)（per-sample coding theorem =
> `awgn_achievability` / `awgn_converse`、Phase 3/4 の per-sample 資産）
> **Facts ledger**: `docs/shannon/shannon-facts.md`（あれば。machine 裏付けは code の `#print axioms` を SoT とし prose にキャッシュしない）

## 進捗

- [x] Phase 0 — Mathlib + InformationTheory API 在庫 ✅（commit 8bf07545）
- [~] Phase 1 — operational infra 🔄 **[FALSIFIED: def が degenerate/under-specified、`@audit:defect` 済。Phase 1-fix で再設計]**（commit 7e354045）
- [~] Phase 5-min — wire + Option A README infra 🔄 **[FALSIFIED: 着地した mainline は false-as-framed、2026-07-14 tier-2 audit OVERTURNED]**（commit b8770fce / ff32ec82）
- [ ] **Phase 1-fix — faithful band-limit + continuous-codeword redesign 🚧 [新 mainline blocker = 次 leg]**
- [ ] Phase 3 — achievability closure（`contAwgn_ge_shannonHartley`、既 skeleton `ShannonHartleyAchievability.lean`）📋 **[Phase 1-fix に gated、fix 後 un-blocked]**
- [ ] Phase 2 — prolate-DOF スペクトル理論（`timeBandLimitingOp` + 固有値集中）📋 **[stretch / 壁核]**
- [ ] Phase 4 — converse（`contAwgn_le_shannonHartley`、Phase 2 消費）📋 **[stretch]**
- [ ] Phase 5-full — `le_antisymm` 組立 📋 **[stretch / closure]**

## ゴール / Approach

### Goal（最終達成状態）

**mainline（再取得目標、旧「達成済」は OVERTURNED）**: Phase 1 def を faithful・非退化・非循環に
建て直し（Phase 1-fix）、`contAwgn_eq_shannonHartley`（`@[entry_point]`）を **true-as-framed** な
honest 単一 wall-sorry として復帰（body = `sorry -- @residual(wall:nyquist-2w-dof)`）。
`IsTwoWDegreesOfFreedom` load-bearing predicate の除去自体は有効（`ShannonHartley.lean` から消滅済）だが、
それを受けた operational def が degenerate/under-specified で命題を空にしていた（下記「def-fix の必要」）。

**stretch（残）**: その wall-sorry を genuine 証明で除去し `contAwgn_eq_shannonHartley` を 0-sorry
（`@audit:ok`）に復帰。真の壁核は converse 側の単一 `wall:nyquist-2w-dof`（prolate-DOF）に閉じ込め済
（**ただし壁が genuine なのは statement が true になった後**）。

honesty bar 不変（CLAUDE.md「検証の誠実性」）: genuine に建て、真に詰まる sub-wall のみ
honest `sorry + @residual(wall:<slug>)` で分解。**load-bearing hyp / 循環 def / `:True` slot は禁止**。

### def-fix の必要（overturn の根 = 2 独立ルート、詳細はコード stamp が SoT）

1. **degenerate `IsBandlimited`**（`@audit:defect(degenerate)`、ShannonHartleyOperational.lean:~86）:
   L¹ `Real.fourierIntegral`（`𝓕`）を使うため非 L¹ 信号で junk-0 = すべての genuine 帯域制限 L² 信号
   （非 L¹）で述語が vacuously 成立し何も制約しない。
2. **pointwise-vs-a.e. gap**（`@audit:defect(false-statement)`、~line 213）: `sampledSignal` は pointwise
   `f(node)` を読むが `encoder_power`/`𝓕` は a.e. class しか見ない。`0` a.e. で 1 node だけ巨大値の codeword が
   全 field を満たしつつサンプル無限大 → `ContAwgnCode.encoder` に continuity/L²-membership field が無いため
   固定 `IsBandlimited` 下でも生存。
帰結: message 集合 unbounded ⇒ `contAwgnMaxMessages = Nat.sSup(unbounded) = 0` ⇒ capacity `0 ≠ W·log(1+P/(N₀W)) > 0`。
（2026-07-14 の非退化論法は暗に Parseval = genuine 帯域制限**連続**代表の存在を仮定していた。）

### Approach（解の全体形 = 戦略）

Shannon-Hartley の operational 版 = **サンドイッチ**:
`bandlimitedAwgnCapacity ≤ contAwgnOperationalCapacity`（achievability, Phase 3）
`∧ contAwgnOperationalCapacity ≤ bandlimitedAwgnCapacity`（converse, Phase 4）
→ `le_antisymm` で等号（Phase 5-full）。

戦略の要は **2W という次元定数を def に埋めず、証明の 2 方向から emerge させる**（`2W`・`⌊2WT⌋` を
def に含めない C3 の意図は Phase 1-fix でも継承。**旧 Phase 1 def はこの形は満たしたが degenerate/under-specified
で命題を空にしていた** → Phase 1-fix で faithful 化）:

- **achievability（≥）は synthesis 補間 + per-sample coding で閉じる（壁非依存、faithful def 前提で GO）**: 真間隔
  `Δ = T/n`（`n = ⌊2WT⌋`）でサンプリング → `awgn_achievability`（既所有、genuine）で
  `≈ exp(T·W·log(1+SNR))` メッセージの codebook → **synthesis bridge**（任意有限サンプルベクトルを補間する
  帯域制限信号を構成、`whittaker_shannon_bandlimited` の analysis 逆向き）で連続信号化。prolate（Phase 2）を
  要さない。**edge-effect は dissolve**（`encoder_power` は in-window `∫_{[0,T]}f²` だけ課金、sinc isometry で
  全直線 `∫_ℝ f² ≤ T·P` ⇒ `∫_{[0,T]} ≤ ∫_ℝ ≤ T·P`、窓外への sinc tail 漏れは電力制約を**緩める** = tolerate でない）。
- **converse（≤）は prolate-DOF 上界が本質**: 受信信号を上位 `≈2WT` 個の prolate 固有関数に射影
  → `awgn_converse`（既所有、genuine）+ 次元カウント。**ここだけが `wall:nyquist-2w-dof` を要する**
  （time-and-band limiting operator `P_W Q_T P_W` の固有値集中 = Landau-Pollak-Slepian、Mathlib 不在）。

したがって **真の壁は converse 側の単一核 `nyquist-2w-dof`（Phase 2 → Phase 4）に閉じ込められる**。
Phase 1 の周辺インフラと Phase 3 achievability は壁でない（in-project 定義・証明可能）。

### route（DAG 選択 + 起点、overturn 後に再シーケンス）

旧「mainline 達成済 → stretch」は無効。攻略順は
**Phase 1-fix（def 再設計、新 mainline blocker・起点）→ Phase 3（achievability closure、fix 後 un-blocked）
→ Phase 2（prolate 壁核・最深）→ Phase 4（converse）→ Phase 5-full（サンドイッチ組立）**。

**起点 = Phase 1-fix**。Phase 1 def が degenerate/under-specified の間は achievability の GO 論法
（edge-effect dissolve = exact sinc isometry）も、`contAwgnMaxMessages_bddAbove` も成立しない
（既存 skeleton の 5 sorry は fix 後に初めて genuine 化）。2026-07-15 の Phase 3 GO/NO-GO 判定は
faithful def を前提にしており、**Phase 1-fix 完了までは条件付き**。詳細 → Phase 1-fix / Phase 3 節。

---

## 設計制約 — 循環罠 #2 回避（非循環設計の受入基準・SoT）

proof-pivot-advisor 名指しの循環罠: **連続時間 code を「長さ `⌊2WT⌋` のサンプルベクトルに制限」して
定義してはならない**。それは converse の DOF 限界（Landau-Pollak-Slepian）を def に埋め込む循環
（= 連続容量をサンプル済有限次元容量として定義に等価化）で、還元定理が `rfl` 化し証明が空になる。

**非循環設計の受入基準**（Phase 1 で全て充足済。Phase 3/4 の「循環チェック」欄で再照合）:

1. **C1 — codeword 空間**: codeword は `[0,T]` 上の**任意の帯域制限 `[-W,W]` 信号**（essentially
   time-limited to `[0,T]`）を許す。固定長サンプルベクトルへの制限は禁止。
   → 実装: `ContAwgnCode.encoder : Fin M → (ℝ → ℝ)`（関数、サンプルベクトルでない ✓）。
2. **C2 — capacity primitive**: `contAwgnOperationalCapacity` を operational 量として定義。**次元定数
   `2W`・`⌊2WT⌋` を一切含まない**。→ 実装: `contAwgnMaxMessages = sSup {M | ∃ code, averageError ≤ ε}`
   に `2W`・`Fin ⌊2WT⌋` 不在 ✓。
3. **C3 — 2W の出所**: 定数 `2W`・`⌊2WT⌋` は Phase 1 のどの def にも現れない。achievability（Phase 3、
   サンプリング rate 選択）と converse（Phase 4、prolate 次元カウント）の**両側から emerge** させる。
4. **C4 — 雑音 / サンプル数**: 雑音は per-sample iid Gaussian、サンプル数 `n` は**自由 ℕ パラメータ**。
   `n = ⌊2WT⌋` に定義段で固定しない。→ 実装: `ContAwgnCode.sampleCount : ℕ`（自由 field ✓）、
   雑音は `errorProbAt` 内 inline `Measure.pi (fun i => gaussianReal (sampledSignalᵢ) (N₀/2))`。

**違反の兆候（tell）**: `contAwgn_eq_shannonHartley` の証明が `rfl` / `unfold` のみで済む、`M(T)` の def に
`Fin (⌊2WT⌋)` が出る、reduction 定理が per-sample capacity をそのまま返す。これらが出たら循環。

---

## Phase 0 — Mathlib + InformationTheory API 在庫 ✅

commit 8bf07545。`docs/shannon/shannon-hartley-operational-inventory.md` に各 Phase feasibility を確定。
mainline GO 判定 + prolate = genuine 壁核の裏取り済。

## Phase 1 — operational infra 🔄 **[FALSIFIED、Phase 1-fix で再設計]**

commit 7e354045。新 file `InformationTheory/Shannon/ShannonHartleyOperational.lean`。def 一式
（`IsBandlimited` / `structure ContAwgnCode` / `sampledSignal` / `errorProbAt` / `averageError` /
`contAwgnMaxMessages` = `sSup{M | …}` / `contAwgnRate` = `limsup_T (log M(T))/T` / `contAwgnOperationalCapacity`
= `⨅ε∈Ioo 0 1 contAwgnRate`）を実装。**当初「全 def が非循環・非退化（C1–C4 充足、`√(T/n)` 正規化が要）」と
記録したが 2026-07-15 に FALSIFIED**: `IsBandlimited`（L¹ `𝓕`）が degenerate、`ContAwgnCode.encoder` に
continuity/L²-membership field が無く pointwise `sampledSignal` が a.e.-class を突破（上記「def-fix の必要」）。
コード stamp が SoT（`@audit:defect(degenerate)` / `@audit:defect(false-statement)`）。C2 primitive の形
（`sSup` に `2W`/`⌊2WT⌋` 不在）と非循環設計意図（C1–C4）は Phase 1-fix でも継承する。
**雑音 route β**（per-sample iid Gaussian を `errorProbAt` に inline、`IsGaussianProcess` 非依存、
proposed wall `cont-awgn-noise-measure` 不発）は overturn の影響外で有効。

## Phase 5-min — wire ✅→🔄 **[着地は FALSIFIED、audit OVERTURNED]**

commit b8770fce（+ Option A README infra = commit ff32ec82）。

- **有効な部分**: `IsTwoWDegreesOfFreedom` / `IsBandlimitedSamplingHypothesis` / `IsBandlimitedKernel` の
  `ShannonHartley.lean` からの除去（load-bearing predicate 消滅）は依然有効。**Option A README honesty infra**
  （`gen_readme_table.ts` が `@residual(wall:*)` 付き documented wall-sorry を許容、listed file は strict 0-sorry
  維持）も再利用可能インフラとして残る。
- **FALSIFIED**: 2026-07-14 の独立 honesty audit（tier-2 PASS、命題 true-as-framed / 非退化）は
  **2026-07-15 に OVERTURNED**（degenerate def で命題が false-as-framed だった）。`contAwgn_eq_shannonHartley`
  の単一 wall-sorry は honest tier-2 ではなく **`@audit:defect(false-statement)`** 状態。
  Phase 1-fix で def を建て直して初めて honest wall-sorry に復帰する。

---

## Phase 1-fix — faithful band-limit + continuous-codeword redesign 🚧 **[新 mainline blocker = 起点]**

**目的**: Phase 1 def を再設計し `contAwgn_eq_shannonHartley` を true-as-framed（finite・band-limited・
非退化）に復帰 → honest な単一 wall-sorry `@residual(wall:nyquist-2w-dof)` を回復（DOF 壁が genuine なのは
**statement が true になった後のみ**）。proof-log: yes。

**M-fix — 在庫 pass（FIRST、coding 前に必須・feasibility-unknown）**: 独立 Mathlib API 在庫（`mathlib-inventory`
の別 leg、`shannon-hartley-operational-inventory.md` に追記）。open design question を先に解く:
- `Lp.fourierTransformₗᵢ`（`MeasureTheory.Lp.fourierTransformₗᵢ`）は `Lp ℂ 2` の a.e.-class 上で動く。
  raw `ℝ → ℝ` 関数に対し「L² 関数で 𝓕-台 ⊆ `[-W,W]`」を **どう clean に述語化するか**。
- 「band-limited L² ⟹ `|f(t)| ≤ √(2W)·‖f‖₂` を満たす連続 canonical 代表を持つ」（Paley-Wiener）が
  Mathlib に在るか / self-build 可能か。**在れば** 連続 L² 関数上の spectral-support `IsBandlimited` +
  1 個の continuity/`Memℒp` field で **両ルートを同時に解消**しうる。**無ければ** Paley-Wiener 連続性補題を
  self-build として計上。→ **feasibility-unknown（この 1 点が Phase 1-fix の最大リスク）**。

**fix recipe（auditor 指定、両ルート必須）**:
- (a) `IsBandlimited` を **L² Fourier transform のスペクトル台**（`Lp.fourierTransformₗᵢ`、台 ⊆ `[-W,W]`）で
  再定義する（L¹ 積分 `𝓕` ではない）→ ルート1（degenerate）解消。
- (b) `ContAwgnCode.encoder` に **L²-membership / continuity field** を追加し、pointwise `sampledSignal` が
  canonical Paley-Wiener 代表（`|f(t)| ≤ √(2W)·‖f‖₂`）を読むようにする → per-sample 電力を finite に回復、
  ルート2（pointwise-vs-a.e.）解消。M-fix で「連続 L² 上の spectral `IsBandlimited` が両ルートを 1 field で
  賄える」と判れば (a)(b) は 1 述語に統合。

**ripple（記録用）**:
- (i) mainline `contAwgn_eq_shannonHartley` は fix 後に honest true-as-framed `@residual(wall:nyquist-2w-dof)` で再着地。
- (ii) Phase 3 skeleton（`ShannonHartleyAchievability.lean`）の `synthSignal_bandlimited` は L²-FT = boxcar で
  **genuine に証明可能**化（現行 degenerate def 下では junk-true）。`contAwgnMaxMessages_bddAbove` +
  `contAwgn_ge_shannonHartley` も **closable** 化（degenerate def 下では un-closable だった）。
- (iii) Phase 4 converse は訂正後の def を消費。
- (iv) **README Option A 脚注は現在 `nyquist-2w-dof` を「true-but-walled」として提示するが実際は false-as-framed**
  = 一時的な dishonesty。def-fix で解消（true 化後は genuine documented wall に戻る）。**この false 状態を
  settled documented wall として outward artifact に提示しない**（README/site には fix 完了まで壁として喧伝しない）。

**依存（DAG edge）**: Phase 0 + M-fix 在庫 → Phase 1-fix。Phase 1-fix → Phase 3 / Phase 4（訂正 def を消費）。
**循環チェック**: 再設計後も設計制約 C1–C4 を再照合（`encoder : Fin M → (ℝ → ℝ)` は関数のまま、
capacity primitive に `2W`/`⌊2WT⌋` を埋めない）。continuity/L²-membership field は codeword の regularity
制約であり DOF 限界を埋め込む循環ではない（射影・次元カウントは converse の証明ステップ）。
**受入基準**: `contAwgn_eq_shannonHartley` が true-as-framed（`@audit:defect` 除去）+ 単一 honest wall-sorry
`@residual(wall:nyquist-2w-dof)` に復帰、`IsBandlimited` の `@audit:defect(degenerate)` 除去。非退化の再確認
（fix 後に `contAwgnMaxMessages` が正 `P` で unbounded → 0 に潰れないこと = 少なくとも 1 code の finite サンプル）。
**概算**: genuine 再設計。def 書換 + Parseval/isometry 再証明 + downstream 再配線で **~300–700 行**
（**Paley-Wiener 連続性が Mathlib 不在なら +~300–600 行 self-build、feasibility-unknown**）。
**retreat line**: Paley-Wiener 連続代表の存在（`|f(t)| ≤ √(2W)‖f‖₂`）が Mathlib 不在で self-build も詰まった
個別補題のみ、その時点で slug を切って honest `sorry + @residual(<class>:<slug>)`。**def を空にする degenerate
再定義 / load-bearing hyp 化は禁止**（`IsBandlimited` を再び vacuous 化しない）。

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
achievability（Phase 3）は Phase 2 に依存しない公算。
**循環チェック**: 本 Phase は def でなく作用素の解析。C3（`2WT` は固有値カウントの**結論**として現れ、
def の入力ではない ✓）。
**受入基準**:
- **proof-done 条件（stretch）**: 作用素定義 + 自己共役 + コンパクト性が genuine、固有値集中が genuine。
- **honest-sorry 分解条件（現実的着地）**: 作用素 + 自己共役 + コンパクト性は **genuine を目標**（Mathlib
  compact operator + spectral theorem の上に建設）。**固有値集中の asymptotic `prolate_eigenvalue_count`
  は最有力の genuine 壁** → body `sorry + @residual(wall:nyquist-2w-dof)`。load-bearing hyp /
  `*Hypothesis` predicate 化は禁止（`nyquist-2w-dof` に集約）。
**feasibility unknown（inventory 反映）**: (a) Mathlib のスペクトル定理が本作用素に適用できる形か
（`IsSelfAdjoint` + compact → 固有値分解）、(b) 固有値の存在・降順列挙が既存 API で取れるか、
(c) 集中不等式（Landau-Pollak-Slepian）の Mathlib 不在は確定（loogle `Found 0`: prolate/Slepian）
→ **self-build ~800-1500 行のスペクトル解析**、詰まれば honest sorry で分解し次 leg。
**retreat line**: `prolate_eigenvalue_count` を `sorry + @residual(wall:nyquist-2w-dof)`。
作用素の自己共役・コンパクト性が Mathlib 不足で詰まる個別補題も同 wall に集約（compound 化しない）。

---

## Phase 3 — achievability closure 📋 **[Phase 1-fix に gated、fix 後 un-blocked]**

**目的**: `bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P`。真間隔 `Δ = T/n`
（`n = ⌊2WT⌋`）サンプリング → per-sample `awgn_achievability`（既所有 genuine）→ **synthesis bridge**
（有限サンプルベクトルを補間する帯域制限信号を構成）で連続信号化。proof-log: yes。**概算 500–850 行**
（+BddAbove leg 分が旧見積 300–600 からの delta）。

**既 skeleton**: `InformationTheory/Shannon/ShannonHartleyAchievability.lean`（11 decl、5 sorry:
`synthSignal_bandlimited` / `synthSignal_sq_integrable` / `synthSignal_energy` /
`contAwgnMaxMessages_bddAbove` / `contAwgn_ge_shannonHartley`）。**これらの 5 sorry は Phase 1-fix
（faithful def）完了後に初めて genuine 化する**: `synthSignal_bandlimited` は L²-FT = boxcar で本物の
帯域制限性を要し（現行 degenerate def では junk-true）、`contAwgnMaxMessages_bddAbove` は `IsBandlimited` が
実制約を課さないと成立しない。→ **Phase 3 は Phase 1-fix に gated**。

**★ code-tag 修正 to-do（実装 owner・次 leg）**: 上記 5 sorry は `@residual(plan:shannon-hartley-op-phase3)`
を付けているが、この slug は解決先ファイルが無い（`docs/shannon/shannon-hartley-op-phase3.md` は不在）。
解決可能な stem は本 plan の filename stem **`shannon-hartley-operational-moonshot-plan`**。
実装 owner が `@residual(plan:shannon-hartley-operational-moonshot-plan)` に書き換える（コードタグが SoT）。

**GO/NO-GO は RESOLVED = GO（壁非依存、ただし faithful def 前提）** — proof-pivot-advisor gate 2026-07-15、
verbatim 照合。**注意: この GO 論法（edge-effect dissolve）は Phase 1-fix 後の faithful def を前提とする**。
`ContAwgnCode.encoder_power`（ShannonHartleyOperational.lean:97）は in-window energy `∫_{[0,T]}f² ≤ T·P`
だけを課金し、全直線 energy `∫_ℝ f²` は exact sinc isometry で既に `≤ T·P`。よって `∫_{[0,T]} ≤ ∫_ℝ ≤ T·P` で
窓外への sinc tail 漏れは電力制約を**緩める**（dissolve、tolerate ではない）。prolate/LPS 次元カウントは
achievability に一切入らない。→ **Phase 3 retreat line（`wall:nyquist-2w-dof` 一部共有）は不発**、
`nyquist-2w-dof` は converse 専用（Phase 2/4）。

**新 file**: `InformationTheory/Shannon/ShannonHartleyAchievability.lean`（imports:
`ShannonHartleyOperational` + `WhittakerShannon`/`NormalizedSinc` + `AWGN.Achievability` + `AWGN.Converse`）。
`ShannonHartleyOperational.lean` を clean に保つ。作成時 `InformationTheory.lean` に import 登録（実装 owner 担当）。
**import cycle なし**（Converse/Achievability/WhittakerShannon は Operational を import しない、verified）。

**主要 theorem（signature スケッチ、Phase 1 実 def 使用）**:

```lean
theorem contAwgn_ge_shannonHartley (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    bandlimitedAwgnCapacity W N₀ P ≤ contAwgnOperationalCapacity W N₀ P := ⟨サンドイッチの ≥ 方向、genuine⟩
```

**構成 leg（3 束）**:

- **leg 1 — bridge sub-module（synthesis + Parseval energy）**。**synthesis ≠ analysis に注意**:
  `whittaker_shannon_bandlimited` は analysis 方向（既帯域制限 f のサンプル）。achievability は synthesis 方向
  = 任意有限サンプルベクトルを補間する帯域制限 f の構成 + その帯域制限性証明（別途要）。再利用資産:
  `NormalizedSinc.sincN_int_eq_kronecker`（NormalizedSinc.lean:95、補間 exactness）+
  `integral_exp_boxcar_eq_sincN`（WhittakerShannon.lean:63、sinc↔boxcar）+ **line**-Plancherel
  `MeasureTheory.Lp.inner_fourier_eq` / `Lp.norm_fourier_eq`（LpSpace.lean:93/89）。**circle 版
  `Lp ℂ 2 haarAddCircle` の sampling engine は使わない**（line-Plancherel が正解）。
- **grid spacing の訂正**: サンプル間隔は真間隔 `Δ = T/n`（`sampledSignal` は spacing `T/n` で標本化、
  ShannonHartleyOperational.lean:110）で、`1/(2W)` **ではない**（`n = ⌊2WT⌋` floor で `Δ ≠ 1/(2W)`）。
  連続 encoder を真間隔 `Δ` で reconstruct し `[−n/(2T), n/(2T)] ⊆ [−W,W]`（`n/(2T) ≤ W`）に帯域制限。
  isometry は EXACT: `∫_ℝ f² = Δ·∑ aᵢ² = ∑(sampledSignalᵢ)² = ∑ cᵢ² ≤ n·P' = ⌊2WT⌋·(P/(2W)) ≤ T·P`。
- **leg 2 — BddAbove crude-converse leg（★ 新規、旧計画欠落）**: `contAwgnMaxMessages = sSup {M : ℕ | …}`
  （ShannonHartleyOperational.lean:138）を `le_csSup` で下界するには集合の **`BddAbove`** が必須。ℕ 上で
  unbounded `sSup` は junk `0` を返す（repo は `Cramer/Cramer.lean` / `ParallelGaussian/PerCoord.lean` で
  この ℕ-sSup-returns-0 罠に既遭遇）。この `BddAbove` は crude converse（任意の有限上界でよい、tight ~2WT
  カウントは不要）ゆえ**壁非依存**。**証明する**（`awgn_converse` を sample vector に適用 + sample-vs-integral
  energy 制御）— **仮説化は禁止**（`≥` 定理に hyp 化すると borderline load-bearing）。→ Phase 3 file が
  `AWGN.Converse` も import する理由（`Achievability` だけでない）。~150–350 行。
- **leg 3 — assembly（`awgn_achievability` 配線）**: 各 `ε ∈ Ioo 0 1` と大 `T` に `sampleCount = ⌊2WT⌋`
  を code の自由 field に代入（C3/C4 ✓）→ `awgn_achievability` で discrete `AwgnCode M n P'`
  （`M ≥ ⌈exp(n·(1/2)log(1+SNR'))⌉ = ⌈exp(T·W·log(1+SNR'))⌉`）→ leg 1 synthesis で連続 encoder 化 →
  `le_csSup`（leg 2 の BddAbove 消費）+ `limsup`/`⨅ε` 操作で `⨅ε contAwgnRate ≥ W·log(1+P/(N₀·W))`。
  **`sampledSignal` √(T/n) 正規化の役割**: 持ち上げた連続 encoder の `sampledSignal` が discrete codeword `cᵢ`
  と一致し、`√(T/n)` isometry で per-sample エネルギー ↔ 連続電力の Parseval 整合 → per-sample SNR = `P/(N₀·W)`
  で `awgn_achievability` の誤り評価がそのまま `averageError ≤ ε` に移る（この正規化がないと oversampling で SNR
  が膨らみ崩れる = 非退化の要）。誤り測度 match は verbatim 確認済（下記）。

**build order（skeleton-first, then bottom-up）**: (0) skeleton = 全 bridge 補題 + BddAbove 補題 +
`contAwgn_ge_shannonHartley` assembly を typed `sorry` で置き type-check done（committable、Parseval 定数 `Δ`
+ 帯域制限区間 `n/(2T)` を pin）→ (1) bridge sub-module（leg 1）を **interpolation-exactness (ii, `sincN_int_eq_kronecker`
再利用, ~30–80) → band-limited synthesis (i, `𝓕` linearity + sinc↔boxcar, ~100–200) → W-scaling/dilation (iv, ~50–150)
→ Parseval energy (iii, line-Plancherel × sinc, ~150–300、最重)** の順で fill → (2) BddAbove leg（leg 2, ~150–350）
→ (3) assembly（leg 3、`le_csSup` + 誤り測度等式 + `limsup`/`⨅ε`）。**bridge-sub-module-first が
top-down-with-sorries より de-risk**（2 つの feasibility unknown は leg 1–2 にあり assembly でない）。

**誤り測度 match（verbatim 確認済）**: `Code.errorProbAt W m = Measure.pi (fun i ↦ W (encoder m i)) (errorEvent m)`
（ChannelCoding/Basic.lean:192）、`awgnChannel N x = gaussianReal x N`（AWGN/Basic.lean:69）⇒ `N = (N₀/2).toNNReal`
+ `sampledSignal = cᵢ` で `ContAwgnCode.errorProbAt`（ShannonHartleyOperational.lean:121）に一致。
`IsAwgnChannelMeasurable` は無条件 dischargeable（`isAwgnChannelMeasurable`, AWGN/ChannelMeasurability.lean）。

**依存（DAG edge）**: Phase 1 + WhittakerShannon/NormalizedSinc（CLOSED）+ AWGN.awgn_achievability（genuine）
+ AWGN.awgn_converse（genuine、leg 2 BddAbove 専用）→ Phase 3。**Phase 2 には依存しない（確定）**。
**循環チェック**: サンプリング rate `2W` / `sampleCount = ⌊2WT⌋` は achievability 側の**構成選択**であり
def の入力でない（C3 ✓）。`contAwgnMaxMessages` を `⌊2WT⌋` サンプルに制限せず、その値以上のメッセージ数を
**達成できる**と示すだけ（C1/C2 ✓）。leg 2 の BddAbove も crude 有限上界（tight 2WT 次元を def に埋めない）ゆえ非循環。
**受入基準**:
- **proof-done 条件（= 目標）**: `≥` を fully genuine 証明（synthesis bridge + Parseval 電力橋 + BddAbove
  crude converse + `awgn_achievability` + 雑音サンプル iid Gaussian）。**Phase 3 に壁は無い**（faithful def 前提の GO）。
**retreat line**: **Phase 3 は wall を生まない**（faithful def 前提の GO で `wall:nyquist-2w-dof` 一部共有は不発）。
予期せぬ Mathlib 不在で詰まった個別補題のみ、その時点で slug を切って honest `sorry + @residual(<class>:<slug>)`
（load-bearing hyp 化・BddAbove の仮説化は禁止）。

---

## Phase 4 — converse 📋 **[stretch]**

**目的**: `contAwgnOperationalCapacity W N₀ P ≤ bandlimitedAwgnCapacity W N₀ P`。
受信信号を上位 `≈2WT` prolate 固有関数（Phase 2）に射影 → `awgn_converse`（既所有 genuine）+ 次元カウント。
proof-log: yes。概算 400–700 行。

**主要 theorem（signature スケッチ）**:

```lean
theorem contAwgn_le_shannonHartley (W N₀ P : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) :
    contAwgnOperationalCapacity W N₀ P ≤ bandlimitedAwgnCapacity W N₀ P := ⟨サンドイッチの ≤ 方向⟩
```

**構成 leg（Phase 1 実 def の使われ方）**:
- Phase 2 `prolate_eigenvalue_count` で「有効次元 ≤ `⌊2WT⌋ + O(log WT)`」を得る（**壁核を消費**）。
- 任意の `ContAwgnCode T W P M` は `sampleCount` を**自由に大きく取れる**（oversampling）が、`sampledSignal`
  の **`√(T/n)` tight-frame 正規化により sampling Gram 作用素が `≈ I`**、有効ランクは `sampleCount` に依らず
  `≈2WT` に留まる。→ **`contAwgnMaxMessages` の上界は `sampleCount` の大きさに依らず prolate DOF カウントで
  bound される**（oversampling が自由 DOF を生まないことが converse の核。`√(T/n)` がこれを保証）。
- 上位固有関数への射影で受信信号を `≈2WT` 次元に還元 → per-letter `awgn_converse`
  （`Real.log M ≤ n·(1/2)log(1+P/N) + binEntropy(Pe) + Pe·log(M-1)`）を適用。
- `limsup(T→∞)` + Fano 項消滅（`Pe → 0`）で `⨅ε contAwgnRate ≤ W·log(1+P/(N₀·W))`。
**依存（DAG edge）**: Phase 1 + Phase 2（`prolate_eigenvalue_count`）+ AWGN.awgn_converse（genuine）→ Phase 4。
**循環チェック（最重要）**: C3 — `⌊2WT⌋` は Phase 2 固有値カウントの**結論**として converse に入り、
capacity def からは来ない ✓。受信信号を射影で次元還元するのは**証明ステップ**であり code def の制限でない
（C1 維持 ✓）。ここで「code をサンプルベクトルに制限」した瞬間に循環化する — 射影は受信側の解析、
codeword 空間は Phase 1 の任意帯域制限信号（`encoder : Fin M → (ℝ → ℝ)`）のまま。
**受入基準**:
- **proof-done 条件**: Phase 2 genuine 前提で `≤` を genuine 証明。
- **honest-sorry 分解条件**: Phase 2 の `prolate_eigenvalue_count` が sorry 状態なら Phase 4 は
  それを transitive 継承し `contAwgn_le_shannonHartley` も `@residual(wall:nyquist-2w-dof)`
  （Phase 4 独自の新 sorry は作らず Phase 2 継承）。
**feasibility unknown**: 射影後の受信分布が `awgn_converse` の要求形（`AwgnCode M n P` + per-letter Gaussian）
に載るか。prolate 固有関数系での Parseval / 電力保存。
**retreat line**: Phase 2 継承の `@residual(wall:nyquist-2w-dof)`。射影 → `awgn_converse` 配線が
Mathlib 不足で詰まる個別補題は同 wall に集約。

---

## Phase 5-full — le_antisymm 組立 📋 **[stretch / closure]**

**目的**: Phase 3 `≥` + Phase 4 `≤` の `le_antisymm` で `contAwgn_eq_shannonHartley` の wall-sorry を除去。
proof-log: no（wiring + 代数再利用、小規模）。概算 30–80 行。

```lean
theorem contAwgn_eq_shannonHartley ... :=
  le_antisymm (contAwgn_le_shannonHartley ...) (contAwgn_ge_shannonHartley ...)
```

- `twoW_perSample_eq_shannonHartley`（代数 leg、既存）+ `bandlimitedAwgnCapacity` / `perSampleAwgnCapacity`
  def を再利用。
- **中間状態**: Phase 3 が genuine・Phase 4 が sorry なら、`contAwgn_eq_shannonHartley` は `≤` 経由で
  `@residual(wall:nyquist-2w-dof)` を継承（`≥` は genuine）。
**依存（DAG edge）**: Phase 3 + Phase 4 → Phase 5-full。
**循環チェック**: 組立後の `contAwgn_eq_shannonHartley` が genuine 等号（`rfl` でない、Phase 3/4 の実証明を経由）
であることを確認。
**受入基準**: `contAwgn_eq_shannonHartley` 0 sorry / 0 residual、`@audit:ok`（= closure）。

---

## Sub-wall map

| Phase | 生む見込みの residual | 位置づけ |
|---|---|---|
| Phase 1（雑音測度） | proposed wall `cont-awgn-noise-measure`（**不発**） | route β（per-sample iid Gaussian を `errorProbAt` に inline）採用で `IsGaussianProcess` 依存が消え、当初 proposed だった雑音測度壁は不要になった（register 追加せず、code 側 slug も生成されない） |
| Phase 2（prolate 固有値集中） | `wall:nyquist-2w-dof`（**最有力・確定的**） | 真の壁核。作用素定義 + 自己共役 + コンパクト性は genuine 目標、**固有値集中 asymptotic のみ**が genuine 壁（loogle `Found 0`: prolate/Slepian、self-build ~800-1500 行）。詰まれば `prolate_eigenvalue_count` を honest sorry で分解 |
| Phase 3（achievability） | **なし（壁非依存、faithful def 前提の GO・Phase 1-fix に gated）** | edge-effect dissolve（`encoder_power` in-window 課金 + exact sinc isometry `∫_ℝf² ≤ T·P`）で `wall:nyquist-2w-dof` 一部共有は不発。全 leg（synthesis bridge + Parseval + BddAbove crude converse + `awgn_achievability`）genuine 目標だが degenerate def 下では un-closable = Phase 1-fix 後に closable |
| Phase 1-fix（def 再設計） | **なし（def-fix、壁生成せず）** | degenerate/under-specified def を faithful 化し `@audit:defect` を除去。retreat は Paley-Wiener 連続性の個別補題のみ（feasibility-unknown）|
| Phase 4（converse） | `wall:nyquist-2w-dof`（**Phase 2 transitive 継承**） | Phase 2 の `prolate_eigenvalue_count` を継承。Phase 4 独自の新 sorry は作らない |
| Phase 5-min（🔄 着地 FALSIFIED） | `@audit:defect(false-statement)`（honest wall ではない） | 現行 `contAwgn_eq_shannonHartley` body の sorry は degenerate def 下で false-as-framed。**2026-07-14 tier-2 audit は OVERTURNED**。Phase 1-fix 後に初めて honest `@residual(wall:nyquist-2w-dof)` に復帰 |

**register 整合**: `nyquist-2w-dof` は `docs/audit/audit-tags.md` Wall name register に既存。**`nyquist-2w-dof` が
genuine documented wall として有効なのは statement が true-as-framed になった後（Phase 1-fix 完了後）のみ** —
現状 `contAwgn_eq_shannonHartley` は `@audit:defect(false-statement)` で、この sorry を「documented wall」として
outward artifact（README/site）に提示しない。register note の consumer 反映は実装 owner の担当（本 plan は
prose に壁事実をキャッシュしない）。各 node の前提: **genuine に詰まったら honest
`sorry + @residual(wall:nyquist-2w-dof)` で分解し次 leg**。load-bearing hyp / `*Hypothesis` predicate 化 /
循環 def / `:True` slot は全 Phase で禁止（CLAUDE.md）。

---

## 依存 DAG / ripple

```
[OVERTURNED] Phase 0 ─► Phase 1 (degenerate def) ─► Phase 5-min (false-as-framed 着地、audit OVERTURNED)

[mainline 再取得] Phase 0 ─► M-fix 在庫 ─► Phase 1-fix (faithful def 再設計・新起点) ─► Phase 3 (achievability closure) ─┐
                                                        │                                                             ├─► Phase 5-full
                                                        └─► Phase 4 (converse) ◄─ Phase 2 (prolate/壁核) ─────────────┘
```

- **mainline blocker（起点）**: `0 → M-fix → 1-fix`。faithful def 再設計で `contAwgn_eq_shannonHartley` を
  true-as-framed + honest 単一 wall-sorry に復帰。
- **fix 後**: `3`（achievability closure、既 skeleton の 5 sorry を genuine 化）→ `2 → 4`（converse、壁核）→ `5-full`。
- **ripple**: `IsTwoWDegreesOfFreedom` 削除は完了済で有効（consumer 影響 ShannonHartley.lean 内に閉じる）。
  新 file `ShannonHartleyAchievability.lean` は既存 + `InformationTheory.lean` に import 登録済
  （import cycle なし = Converse/Achievability/WhittakerShannon は Operational を import しない）。
  Phase 1-fix の def 書換 ripple: `IsBandlimited` / `ContAwgnCode` の consumer は Operational + Achievability の
  2 file（実装 owner は `dep_consumers` で blast radius を確認して書換）。

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active な判断のみ残す（≤ 10 entry）。

1. **🔄 mainline OVERTURNED = false-as-framed defect（2026-07-15、commit e711aa03）**: 既 publish 済
   `contAwgn_eq_shannonHartley` は現行 Phase 1 def の下で `P > 0` で FALSE。Phase 3 実装中に発見、fresh
   `honesty-auditor` が full machine verification で確認、2026-07-14 tier-2 audit を OVERTURN。2 独立ルート
   （① degenerate `IsBandlimited`=L¹`𝓕` junk-0、② pointwise-vs-a.e. gap = encoder に continuity/L² field 不在）。
   詳細プロセスはコード stamp が SoT（`@audit:defect(degenerate)` / `@audit:defect(false-statement)`）。→ 新 mainline
   blocker = **Phase 1-fix**（L²-FT spectral-support `IsBandlimited` + Paley-Wiener 連続代表 field）。再シーケンス:
   `1-fix → 3 → 2/4 → 5-full`。Paley-Wiener 連続性の Mathlib 有無が最大リスク（feasibility-unknown、M-fix 在庫で先に解く）。
2. **Phase 3 achievability GO 論法は faithful def が前提**: sinc-tail edge-effect dissolve（exact sinc isometry
   `∫_ℝf² ≤ T·P`）+ BddAbove crude-converse（ℕ-sSup-returns-0 罠、`le_csSup` 前提、仮説化禁止）+ synthesis
   bridge/line-Plancherel の 3 点は proof-pivot-advisor gate 2026-07-15 で verbatim 確定したが、**degenerate def
   下では成立せず Phase 1-fix に gated**（既 skeleton の 5 sorry は fix 後に genuine 化）。`nyquist-2w-dof` は
   converse 専用（Phase 2/4）。
3. **真の壁核は converse 側の `nyquist-2w-dof` 単一**: Phase 2（固有値集中）→ Phase 4（converse 上位カウント）に
   閉じ込める。Phase 1-fix / Phase 3 achievability は壁非依存を第一目標（壁が genuine なのは statement true 化後）。
4. **`sampledSignal` の `√(T/n)` 正規化は必要だが非退化に不十分**: per-sample↔連続電力 Parseval 整合
   （SNR = `P/(N₀·W)`）と converse tight-frame（oversampling が DOF を生まない）に要るが、**正規化だけでは
   非退化を保証しない** — pointwise-vs-a.e. gap（decision log #1 ルート②）が正規化を突破し `contAwgnMaxMessages`
   を 0 に潰す。非退化は Phase 1-fix の continuity/L² field が担う。`sampleCount` は自由 field（C4）に保つ。
5. **循環罠 #2 は設計制約節が SoT**: 各 Phase の「循環チェック」欄で C1–C4 を照合。Phase 1-fix の
   continuity/L²-membership field は codeword regularity（DOF 限界の埋め込みではない）。Phase 4 の受信信号射影は
   「証明ステップであって code def の制限でない」を厳守（codeword 空間は `encoder : Fin M → (ℝ → ℝ)` のまま）。

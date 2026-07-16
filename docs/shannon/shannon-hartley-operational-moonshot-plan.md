# Shannon-Hartley operational capacity closure ムーンショット計画 🌙

**Status**: ✅ **mainline RESTORED（2026-07-15、Phase 1-fix 着地、commit 7c3afc86、独立 honesty audit PASS）**。
Phase 1-fix（def 再設計）で 2 defect root（degenerate L¹-`𝓕` `IsBandlimited` / a.e.-class encoder gap）を
解消し、`contAwgn_eq_shannonHartley` は **true-as-framed** な honest 単一 wall-sorry
`@residual(wall:nyquist-2w-dof)` に復帰（`nyquist-2w-dof` は statement true 化後の genuine documented wall）。
コード側 SoT = `ShannonHartleyOperational.lean`（`@audit:defect` 除去済、詳細は Phase 1-fix「着地」節）。
**残 open work**: (1) shared bridge `l2Fourier_eq_fourierIntegral`（+ inverse sibling）+ `bandlimited_sup_bound` = ✅
**proof-done・sorryAx-free・独立 audit PASS**（commit 9d8608a8/40c2e449/30b59a15）。(2) Phase 3 achievability closure：
**leg 1（synthSignal band-limit/energy 3 sorry）= ✅ proof-done・audit PASS（commit 89ede2a3/646605c7）**。
残る Phase 3 **leg 2（`contAwgnMaxMessages_bddAbove`）+ leg 3（`contAwgn_ge_shannonHartley` assembly）は
2026-07-15 に WALL-GATED と判明**（proof-pivot-advisor verdict 2、下記 Phase 3 節）: leg 2 の `BddAbove` は
標本エネルギー↔窓エネルギーの時間帯域集中（prolate/LPS）= mainline と同一 `wall:nyquist-2w-dof` を要し、
旧「crude・壁非依存」判定は under-estimation だった。leg 3 は ℕ-`sSup` の `le_csSup` が leg 2 の `BddAbove` を
消費するため transitively 同一壁に gated。→ **Phase 3 achievability closure は壁ブロック**（コード側は
leg 2 = `@residual(wall:nyquist-2w-dof)`、leg 3 = `@residual(plan:…)`（assembly は書ける plan-work だが
`le_csSup` 経由で leg 2 の壁を prerequisite として消費、独立監査 2026-07-15 で単一壁の二重計上を避け plan: に確定）。
full closure には (a) prolate 壁 self-build（Phase 2、~1000-2000 行）
か (b) 容量 def の achievable-rate 形への再設計（achievability を converse の boundedness から decouple）が前提。
stretch（Phase 2/4/5-full）は不変。honesty bar 不変（CLAUDE.md「検証の誠実性」）。

> **Parent**: [`../textbook-roadmap.md`](../textbook-roadmap.md) §Ch.9 Shannon-Hartley（Ch.9.6）
> **関連**: [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md)
> （sampling theorem = CLOSED、Phase 3/4 の信号↔サンプル橋）/
> [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)（per-sample coding theorem =
> `awgn_achievability` / `awgn_converse`、Phase 3/4 の per-sample 資産）
> **Facts ledger**: `docs/shannon/shannon-facts.md`（あれば。machine 裏付けは code の `#print axioms` を SoT とし prose にキャッシュしない）

## 進捗

- [x] Phase 0 — Mathlib + InformationTheory API 在庫 ✅（commit 8bf07545）
- [~] Phase 1 — operational infra 🔄 **[FALSIFIED → Phase 1-fix で再設計済]**（commit 7e354045）
- [x] M-fix — 在庫 pass（faithful band-limit design question 解決）✅（commit 5aeb2f92）
- [x] **Phase 1-fix — faithful band-limit + continuous-codeword redesign ✅（commit 7c3afc86、独立 honesty audit PASS）**
- [~] Phase 5-min — wire + Option A README infra 🔄 **[旧着地 FALSIFIED、Phase 1-fix で mainline 復帰済]**（commit b8770fce / ff32ec82）
- [x] **l2Fourier bridge（fwd+inv）+ bandlimited_sup_bound ✅ proof-done・audit PASS（commit 9d8608a8/40c2e449/30b59a15）**
- [~] Phase 3 — achievability closure（`contAwgn_ge_shannonHartley`）🔄 **leg 1（synthSignal band-limit/energy）= ✅ audit PASS（commit 89ede2a3/646605c7）**。**leg 2（BddAbove）+ leg 3（assembly）= 2026-07-15 WALL-GATED（`wall:nyquist-2w-dof`、mainline と同一壁）**。壁ブロックゆえ Phase 3 単独では closure 不可 → 壁 self-build（Phase 2）か 容量 def 再設計が前提
- [~] Phase 2 — prolate-DOF スペクトル理論（`timeBandLimitingOp` + 固有値集中）🔄 **[user 指示で全理論自前構築 開始（leg 9+）: Leg A✅ → Leg B コンパクト性 dispatch 中 → Leg C 列挙 → WSEB → Leg E LPS count]** → [shannon-hartley-phase2-spectral-plan.md](shannon-hartley-phase2-spectral-plan.md)
- [ ] Phase 4 — converse（`contAwgn_le_shannonHartley`、Phase 2 消費）📋 **[stretch]**
- [ ] Phase 5-full — `le_antisymm` 組立 📋 **[stretch / closure]**

## ゴール / Approach

### Goal（最終達成状態）

**mainline（達成済、commit 7c3afc86）**: Phase 1-fix で def を faithful・非退化・非循環に建て直し、
`contAwgn_eq_shannonHartley`（`@[entry_point]`）は **true-as-framed** な honest 単一 wall-sorry
（body = `sorry -- @residual(wall:nyquist-2w-dof)`）に復帰済（独立 audit PASS）。
`IsTwoWDegreesOfFreedom` load-bearing predicate 除去（`ShannonHartley.lean` から消滅済）も有効。

**stretch（残）**: その wall-sorry を genuine 証明で除去し `contAwgn_eq_shannonHartley` を 0-sorry
（`@audit:ok`）に復帰。真の壁核は converse 側の単一 `wall:nyquist-2w-dof`（prolate-DOF）に閉じ込め済
（**ただし壁が genuine なのは statement が true になった後**）。

honesty bar 不変（CLAUDE.md「検証の誠実性」）: genuine に建て、真に詰まる sub-wall のみ
honest `sorry + @residual(wall:<slug>)` で分解。**load-bearing hyp / 循環 def / `:True` slot は禁止**。

### def-fix の背景（overturn = 2 独立ルート、Phase 1-fix で解消済・history）

旧 Phase 1 def は 2 root で命題を空にしていた: (1) degenerate `IsBandlimited`（L¹-`𝓕` junk-0）、
(2) pointwise-vs-a.e. gap（encoder に continuity/L²-membership field 不在）。帰結は
`contAwgnMaxMessages = Nat.sSup(unbounded) = 0`。両 root は Phase 1-fix（着地節）で dissolve 済 =
コード側 `@audit:defect` 除去済（現状 false-as-framed ではない、以下は解決した設計上の理由の記録）。

### Approach（解の全体形 = 戦略）

Shannon-Hartley の operational 版 = **サンドイッチ**:
`bandlimitedAwgnCapacity ≤ contAwgnOperationalCapacity`（achievability, Phase 3）
`∧ contAwgnOperationalCapacity ≤ bandlimitedAwgnCapacity`（converse, Phase 4）
→ `le_antisymm` で等号（Phase 5-full）。

戦略の要は **2W という次元定数を def に埋めず、証明の 2 方向から emerge させる**（`2W`・`⌊2WT⌋` を
def に含めない C3 の意図は Phase 1-fix でも継承。**旧 Phase 1 def はこの形は満たしたが degenerate/under-specified
で命題を空にしていた** → Phase 1-fix で faithful 化）:

- **achievability（≥）の信号構成は synthesis 補間 + per-sample coding で閉じる（壁非依存）が、operational な `BddAbove`（leg 2）は `wall:nyquist-2w-dof` family を要する（2026-07-15 是正）。Phase 2 sub-plan の中心問題 verdict: BddAbove ⟸ スカラー WSEB（`awgn_converse` trace 境界、子 Leg W→Leg D、作用素論を経由しない）。WSEB status = leg 9 で決着: 単標本 atom は数値 2 独立法で TRUE（FALSE/def-fix 排除）だが self-build は GENUINE WALL（~800–1500 行 prolate/LPS 理論、Mathlib 完全不在、`lean-implementer` machine verdict）。⟹ (b) 正面突破は失敗、honest sorry 維持、次は user-decision（子 plan「route」3 択）。settled-facts → `shannon-hartley-facts.md`**: 真間隔
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

### route（DAG 選択 + 次アクション）

Phase 1-fix 完了（commit 7c3afc86）で mainline は honest wall-sorry に着地。残る攻略順は
**bridge `l2Fourier_eq_fourierIntegral`（`bandlimited_sup_bound` を genuine 化、mainline-adjacent 次アクション）
→ Phase 3（achievability closure、既 skeleton の 5 sorry を fill、Phase 1-fix で un-blocked）
→ Phase 2（prolate 壁核・最深）→ Phase 4（converse）→ Phase 5-full（サンドイッチ組立）**。

**次アクション = bridge lemma fill**。`l2Fourier_eq_fourierIntegral`（L²-FT ↔ pointwise L¹ `Real.fourierIntegral`
の L¹∩L² 上一致）を埋めれば `bandlimited_sup_bound` が genuine 化する（~150–250 行、壁でない）。その後
Phase 3 achievability の GO 論法（edge-effect dissolve = exact sinc isometry、`contAwgnMaxMessages_bddAbove`）は
faithful def の下で有効 = 5 sorry が genuine 化可能。詳細 → Phase 1-fix「着地」/ Phase 3 節。

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

## Phase 1 / Phase 5-min — retired（Phase 1-fix に統合）

- **Phase 1 — operational infra**（commit 7e354045）: `ShannonHartleyOperational.lean` の def 一式実装。
  当初 def が degenerate/under-specified で 2026-07-15 に FALSIFIED → **Phase 1-fix で再設計済**（着地節）。
  C2 primitive 形（`sSup` に `2W`/`⌊2WT⌋` 不在）+ 非循環設計意図 C1–C4 + 雑音 route β（per-sample iid
  Gaussian を `errorProbAt` に inline、proposed wall `cont-awgn-noise-measure` 不発）は Phase 1-fix でも継承・有効。
- **Phase 5-min — wire**（commit b8770fce / ff32ec82）: `IsTwoWDegreesOfFreedom` 等 load-bearing predicate の
  `ShannonHartley.lean` からの除去 + Option A README honesty infra（`gen_readme_table.ts` が `@residual(wall:*)`
  documented wall-sorry を許容）は有効な再利用インフラ。旧着地は false-as-framed で 2026-07-14 audit OVERTURNED
  だったが Phase 1-fix で mainline 復帰済。

---

## Phase 1-fix — faithful band-limit + continuous-codeword redesign ✅ **[DONE、commit 7c3afc86、audit PASS]**

**目的**: Phase 1 def を再設計し `contAwgn_eq_shannonHartley` を true-as-framed（finite・band-limited・
非退化）に復帰 → honest な単一 wall-sorry `@residual(wall:nyquist-2w-dof)` を回復。M-fix 在庫（commit 5aeb2f92）で
open design question（L² 関数上の spectral `IsBandlimited` 述語化 + Paley-Wiener 連続代表の Mathlib 有無）を先行解決。

### 着地（2026-07-15、commit 7c3afc86、独立 honesty audit PASS）

- **(a)** `IsBandlimited` を **L²-Fourier スペクトル台**で再定義（signature は `(ℝ→ℝ)` 維持 = option X、内部で
  complexify）→ degenerate L¹-`𝓕` junk-0 root 解消。
- **(b)** `ContAwgnCode` に regularity field `encoder_memLp` + `encoder_continuous` を追加 → pointwise-vs-a.e. gap 解消
  （codeword が canonical 連続 L² 代表を読む）。
- **(c)** Paley-Wiener sup bound は **field でなく派生 theorem** `bandlimited_sup_bound` として着地、body =
  `sorry -- @residual(plan:shannon-hartley-operational-moonshot-plan)`。
- **(d)** 唯一の genuine self-build gap = shared bridge lemma **`l2Fourier_eq_fourierIntegral`**（L²-FT ↔ pointwise
  L¹ `Real.fourierIntegral` の L¹∩L² 上一致、~150–250 行の tempered-distribution plumbing、**壁でない**）。
- **(e)** audit PASS: 2 false-as-framed root 双方 dissolve、新 field は regularity/非 load-bearing、wall は genuine。
- **auditor clarification（future closer 向け注意）**: `bandlimited_sup_bound` が与えるのは **full-line** の
  `|f(t)| ≤ √(2W)·‖f‖₂` 束（`‖f‖₂` は全直線 L² ノルム）。full-line → window energy `∫_{[0,T]}f² ≤ T·P` の tie は
  sup bound 単独ではなく `nyquist-2w-dof` の band-limit/essential-time-limitation 構造が供給する
  （sup bound だけで window-energy sample boundedness が出ると誤読しないこと）。

**循環チェック（充足）**: C1–C4 再照合済（`encoder : Fin M → (ℝ → ℝ)` は関数のまま、capacity primitive に
`2W`/`⌊2WT⌋` 不在）。continuity/L²-membership field は codeword regularity であり DOF 限界の埋め込みではない。
**README ripple**: Option A 脚注の `nyquist-2w-dof` は fix 完了で genuine documented wall に復帰（一時 false 状態は解消）。

---

## Phase 2 — prolate-DOF スペクトル理論 📋 **[stretch / 壁核・最深]**

> **サブ計画**: [`shannon-hartley-phase2-spectral-plan.md`](shannon-hartley-phase2-spectral-plan.md)
> （中心問題 verdict: **Phase 3 BddAbove ⟸ スカラー WSEB** via `awgn_converse` trace 境界（Leg W → Leg D）で
> **作用素論を経由しない**。作用素スペクトル鎖 Legs A✅/B/C/E は **Phase-4 tight-count 専用**。**WSEB status =
> leg 9 決着: TRUE（数値 2 独立法、FALSE 排除）だが self-build は GENUINE WALL（~800–1500 行 prolate 理論、
> machine verdict）**。旧「BddAbove は定性コンパクト性で閉じる」は tail-eigenvalue/trace gap で route WRONG と判明）。
> settled-facts → [`shannon-hartley-facts.md`](shannon-hartley-facts.md)。在庫 = [`shannon-hartley-phase2-spectral-inventory.md`](shannon-hartley-phase2-spectral-inventory.md)。以下は pointer。

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

**GO/NO-GO は PARTIAL（2026-07-15 再判定）**: 信号「構成」（leg 1）と電力制約充足は GO・壁非依存だが、
**leg 2 の `BddAbove` は WALL-GATED（`wall:nyquist-2w-dof`）**。旧「Phase 3 全体が壁非依存」は under-estimation。
- **有効な部分（GO）**: achievability の連続 encoder を `synthSignal`（synthesized 信号）で構成する限り、
  `∫_ℝ f² = Δ·∑aᵢ²`（exact sinc isometry、leg 1 の `synthSignal_energy` で proof-done）ゆえ全直線 energy が
  discrete energy と一致し、`ContAwgnCode.encoder_power`（in-window `∫_{[0,T]}f² ≤ ∫_ℝ f² = Δ·∑aᵢ² ≤ T·P`）は
  素直に充足。窓外 sinc tail は制約を**緩める**（dissolve）。この edge-effect dissolve は **構成した信号にのみ**成立。
- **壁に当たる部分（NO-GO / 撤退ライン発火）**: 容量が `contAwgnMaxMessages = Nat.sSup {M | …}` と定義されるため、
  achievability の下界 `sSup ≥ M₀` を `le_csSup` で取るには集合の `BddAbove`（= leg 2）が必須。`BddAbove` は
  **任意の** `ContAwgnCode`（synthesized とは限らない）を扱う converse 的主張で、そこでは上の isometry が使えず
  「窓内エネルギー ≤ T·P から標本エネルギーを一様に抑える」= 時間帯域集中（prolate/LPS）= `nyquist-2w-dof` 壁が要る。
  → **Phase 3 retreat line は leg 2 で発火**、`nyquist-2w-dof` は achievability（leg 2/3）と converse（Phase 2/4）で
  **共有**される（旧「converse 専用・不発」は誤り）。**エビデンス**: proof-pivot-advisor 2026-07-15 verdict 2（crude ルート
  3 抜け穴 a/b/c を潰し反証、`awgn_converse` 適用は uniform 標本エネルギー境界を要し それ自体が壁）。tell = 本 plan の
  Phase 4（converse）が同一「M を上から抑える」ジョブを既に `wall:nyquist-2w-dof` と宣言（自己矛盾）。

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
- **leg 2 — BddAbove leg 🧱 WALL-GATED（2026-07-15 再判定、旧「crude・壁非依存」判定を撤回）**:
  `contAwgnMaxMessages = sSup {M : ℕ | …}`（ShannonHartleyOperational.lean:392）を `le_csSup` で下界するには
  集合の **`BddAbove`** が必須。ℕ 上で unbounded `sSup` は junk `0` を返す（repo は `Cramer/Cramer.lean` /
  `ParallelGaussian/PerCoord.lean` でこの ℕ-sSup-returns-0 罠に既遭遇）。**旧見立て（crude 有限上界ゆえ壁非依存、
  `awgn_converse` を sample vector に適用 + energy 制御で ~150-350 行）は under-estimation だった**。`awgn_converse`
  で M を有限に抑えるには標本エネルギー `E = (T/n)∑ᵢ f(tᵢ)²` を **コード族全体 + `sampleCount = n` について一様**に
  抑える必要があるが、`ContAwgnCode` は**窓内**エネルギー `∫_{[0,T]}f² ≤ T·P` しか課さず、`bandlimited_sup_bound` は
  **全直線** `‖f‖₂`（無制約）でしか点値を抑えられない。窓内標本エネルギー↔窓内エネルギーの結合は
  時間帯域集中（prolate/LPS）= **`wall:nyquist-2w-dof`（mainline と同一壁）**。命題は真だが crude な中間境界は無く、
  finiteness そのものが集中定理を要する。**仮説化は依然禁止**（`≥`/BddAbove の core を hyp 化 = load-bearing tier-5、
  全直線エネルギー field 追加も壁の偽装）。コード側は `sorry + @residual(wall:nyquist-2w-dof)` に是正済。
  → Phase 3 file が `AWGN.Converse` も import する理由（converse-flavored な BddAbove）。壁核 self-build は Phase 2 と共有。
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

**依存（DAG edge）**: Phase 1 + WhittakerShannon/NormalizedSinc（CLOSED）+ AWGN.awgn_achievability（genuine、leg 3）
→ Phase 3 leg 1/3。**leg 2（BddAbove）は Phase 2 の prolate 壁核と同一 `wall:nyquist-2w-dof` に依存する**
（2026-07-15 判定、旧「Phase 2 には依存しない（確定）」は撤回）。`awgn_converse` は BddAbove 単独では標本エネルギーの
一様境界を供給できず、そこが壁。
**循環チェック**: サンプリング rate `2W` / `sampleCount = ⌊2WT⌋` は achievability 側の**構成選択**であり
def の入力でない（C3 ✓）。`contAwgnMaxMessages` を `⌊2WT⌋` サンプルに制限せず、その値以上のメッセージ数を
**達成できる**と示すだけ（C1/C2 ✓、非循環は保持）。ただし leg 2 の BddAbove は crude 有限上界では取れず
（旧記述は誤り）、時間帯域集中 = `wall:nyquist-2w-dof` を要する。
**受入基準**:
- **proof-done 条件（= 目標）**: `≥` を fully genuine 証明（synthesis bridge + Parseval 電力橋 + BddAbove
  + `awgn_achievability` + 雑音サンプル iid Gaussian）。**leg 1（synthesis/energy）= 壁非依存で proof-done 済**。
  **leg 2（BddAbove）+ leg 3（assembly）= `wall:nyquist-2w-dof` で壁ブロック**（2026-07-15 判定、下記 retreat line）。
**retreat line（2026-07-15 発火）**: **Phase 3 achievability は wall:nyquist-2w-dof を共有する**（旧「Phase 3 は壁を
生まない・一部共有は不発」は撤回。誤りだった）。leg 2 の `BddAbove` が時間帯域集中（prolate/LPS）を要し、leg 3 は
`le_csSup` 経由で leg 2 を消費するため transitively 壁 gated。コード側は `sorry + @residual(wall:nyquist-2w-dof)`
に是正済。**full closure の前提**: (a) 壁核 self-build（Phase 2、prolate 作用素の自己共役・コンパクト性・固有値集中、
~1000-2000 行、詰まれば個別補題を `wall:nyquist-2w-dof` で分解）か (b) 容量 def を achievable-rate 形（rate 達成
predicate の sup）へ再設計し achievability を converse の boundedness から decouple。**依然禁止**: load-bearing hyp 化・
BddAbove/全直線エネルギーの仮説化（壁の偽装）。

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
| Phase 3（achievability） | **leg 1 = なし（synthesis/energy 壁非依存・proof-done 済）／leg 2 (BddAbove) + leg 3 (assembly) = `wall:nyquist-2w-dof`（2026-07-15 是正）** | synthesis 信号の構成（leg 1）は edge-effect dissolve で壁非依存だが、任意コードの `BddAbove`（leg 2）は標本↔窓エネルギー集中を要し main と同一壁。Phase 2 sub-plan の中心問題 verdict（更新）: **BddAbove ⟸ スカラー WSEB `E_s ≤ C(T,W)·∫₀ᵀf²`**（`awgn_converse` trace 境界 + `log(1+x)≤x` で n 一様に潰す、子 Leg W→Leg D）で **作用素論を経由しない**。作用素スペクトル鎖 Legs B/C/E は **Phase-4 tight-count 専用（OFF the BddAbove path）** — count は tail-eigenvalue/trace gap で BddAbove に対し red herring。**WSEB status は probe 保留中**（provable=BddAbove 安く closure / 壁=honest sorry 継続 / false=def-fix escalate） |
| Phase 1-fix（def 再設計） | **`plan:…moonshot-plan`（`bandlimited_sup_bound`）** ✅ | def を faithful 化し `@audit:defect` 除去済（commit 7c3afc86）。残 self-build = bridge `l2Fourier_eq_fourierIntegral`（壁でない、~150–250 行） |
| Phase 4（converse） | `wall:nyquist-2w-dof`（**Phase 2 transitive 継承**） | Phase 2 の `prolate_eigenvalue_count` を継承。Phase 4 独自の新 sorry は作らない |
| Phase 5-min（🔄 旧着地 FALSIFIED → 復帰済） | `@residual(wall:nyquist-2w-dof)`（honest） | 旧 mainline は degenerate def 下で false-as-framed（2026-07-14 audit OVERTURNED）だったが、Phase 1-fix で `contAwgn_eq_shannonHartley` は honest wall-sorry に復帰済 |

**register 整合**: `nyquist-2w-dof` は `docs/audit/audit-tags.md` Wall name register に既存。Phase 1-fix 完了で
`contAwgn_eq_shannonHartley` は true-as-framed になり、この sorry は genuine documented wall として有効
（`@audit:defect` 除去済）。register note の consumer 反映は実装 owner の担当（本 plan は
prose に壁事実をキャッシュしない）。各 node の前提: **genuine に詰まったら honest
`sorry + @residual(wall:nyquist-2w-dof)` で分解し次 leg**。load-bearing hyp / `*Hypothesis` predicate 化 /
循環 def / `:True` slot は全 Phase で禁止（CLAUDE.md）。

---

## 依存 DAG / ripple

```
[DONE] Phase 0 ─► M-fix 在庫 ─► Phase 1-fix ✅ (faithful def, mainline 復帰) ─► [next] bridge l2Fourier_eq_fourierIntegral ─► Phase 3 (achievability closure) ─┐
                                                                                                                              ├─► Phase 5-full
                                                        Phase 4 (converse) ◄─ Phase 2 (prolate/壁核) ────────────────────────┘
```

- **mainline（達成済）**: `0 → M-fix → 1-fix ✅`。faithful def 再設計で `contAwgn_eq_shannonHartley` は
  true-as-framed + honest 単一 wall-sorry に復帰済（commit 7c3afc86）。
- **next**: bridge `l2Fourier_eq_fourierIntegral` fill（`bandlimited_sup_bound` genuine 化）→ `3`
  （achievability closure、既 skeleton の 5 sorry を genuine 化）→ `2 → 4`（converse、壁核）→ `5-full`。
- **ripple**: `IsTwoWDegreesOfFreedom` 削除は完了済で有効（consumer 影響 ShannonHartley.lean 内に閉じる）。
  新 file `ShannonHartleyAchievability.lean` は既存 + `InformationTheory.lean` に import 登録済
  （import cycle なし = Converse/Achievability/WhittakerShannon は Operational を import しない）。
  Phase 1-fix の def 書換 ripple: `IsBandlimited` / `ContAwgnCode` の consumer は Operational + Achievability の
  2 file（実装 owner は `dep_consumers` で blast radius を確認して書換）。

---

## 判断ログ

append-only。決着済 entry は削除（git が履歴）、active な判断のみ残す（≤ 10 entry）。

1. **✅ mainline OVERTURN は Phase 1-fix で RESOLVED（2026-07-15、commit 7c3afc86、audit PASS）**: 2026-07-14
   tier-2 audit を覆した 2 root（① degenerate L¹-`𝓕` `IsBandlimited`、② pointwise-vs-a.e. encoder gap）は
   def 再設計（L²-FT spectral-support + `encoder_memLp`/`encoder_continuous` field）で dissolve 済。
   `contAwgn_eq_shannonHartley` は honest 単一 wall-sorry `@residual(wall:nyquist-2w-dof)` に復帰、`@audit:defect` 除去済。
   残: bridge `l2Fourier_eq_fourierIntegral`（壁でない）→ Phase 3。
2. **Phase 3 achievability GO 論法（faithful def 前提、un-gated）**: sinc-tail edge-effect dissolve（exact sinc
   isometry `∫_ℝf² ≤ T·P`）+ BddAbove crude-converse（ℕ-sSup-returns-0 罠、`le_csSup` 前提、仮説化禁止）+ synthesis
   bridge/line-Plancherel の 3 点は proof-pivot-advisor gate 2026-07-15 で verbatim 確定。Phase 1-fix 完了で
   **un-gated**（既 skeleton の 5 sorry が genuine 化可能）。`nyquist-2w-dof` は converse 専用（Phase 2/4）。
3. **真の壁核は converse 側の `nyquist-2w-dof` 単一**: Phase 2（固有値集中）→ Phase 4（converse 上位カウント）に
   閉じ込める。Phase 1-fix / Phase 3 achievability は壁非依存を第一目標（壁が genuine なのは statement true 化後）。
4. **`sampledSignal` の `√(T/n)` 正規化は必要だが非退化に不十分**: per-sample↔連続電力 Parseval 整合
   （SNR = `P/(N₀·W)`）と converse tight-frame（oversampling が DOF を生まない）に要るが、**正規化だけでは
   非退化を保証しない** — pointwise-vs-a.e. gap（decision log #1 ルート②）が正規化を突破し `contAwgnMaxMessages`
   を 0 に潰す。非退化は Phase 1-fix の continuity/L² field が担う。`sampleCount` は自由 field（C4）に保つ。
5. **循環罠 #2 は設計制約節が SoT**: 各 Phase の「循環チェック」欄で C1–C4 を照合。Phase 1-fix の
   continuity/L²-membership field は codeword regularity（DOF 限界の埋め込みではない）。Phase 4 の受信信号射影は
   「証明ステップであって code def の制限でない」を厳守（codeword 空間は `encoder : Fin M → (ℝ → ℝ)` のまま）。

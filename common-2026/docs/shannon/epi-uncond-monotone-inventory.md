# EPI 無条件化 方針 Y (完全無条件) — 拡張単調性 / ±∞ 退化境界 Mathlib + in-tree 在庫

> **親**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) (傘 moonshot)、
> [`epi-uncond-deffix-monotone-plan.md`](epi-uncond-deffix-monotone-plan.md) (def-fix campaign、P2 拡張単調性 deferred)。
> **scope**: 方針 Y (完全無条件 = a.c. 入力の **有限微分エントロピー precondition `hX_ent`/`hY_ent` も剥がす** +
> 一般測度) の残壁 feasibility。**read-only inventory** — 実装・計画起草はしない。

## 一行サマリ

**方針 Y の残壁を実現する API のうち、EReal 算術・Fatou・条件付けエントロピー機構は実体 100% 既存
(in-tree + Mathlib)。だが核心 2 壁 — (W-Y1) 拡張単調性の +∞ 伝播 `h(W)=+∞ ⟹ h(W+V)=+∞`、(W-Y2)
entropy power 弱収束半連続性 — は Mathlib 完全不在 + in-tree 未実装で、自作必要は 2 件。**
撤退ライン **L-Uncond-3-scope** (方針 X 縮退) は本調査では **発動しない** (方針 Y は数学的に true、
壁は genuine だが gateway atom 不在ではない) が、ROI 判断は別問題。

> **⚠ 2026-06-07 machine 再評価で scope 訂正 (§1「自作が必要な要素」の +∞ 伝播見積りは過小)**:
> 本 inventory L199-201/223-226 の「+∞ 伝播 = plan-closeable plumbing ~80-150 行、Mathlib 壁でない」は
> **過小評価**だった。machine 証拠: Mathlib の Jensen は全て `Integrable (g∘f)` 要求 (B_{W+V}<⊤ が ⊤ 枝で破綻)、
> `Measure.conv` entropy-monotone / lintegral Jensen = loogle Found 0、advisor の enorm A=⊤ 案は循環。
> 真の攻略 = EReal-conditioning 単調性 (multi-session moonshot 規模)。**SoT = `epi-uncond-deffix-monotone-plan.md` §7**。
> 本 inventory の +∞ 伝播 工数欄は信用せず §7 を読む (CLAUDE.md 由来の「在庫が capstone Case 2 の tactic body を
> 読まず density route 工数を出した」過大評価の実例)。

**最重要発見**: in-tree `EPIG2KLFatouLSC.lean:112` `klDiv_le_liminf_of_ae_tendsto` が **KL の liminf
半連続性を genuine (`@audit:ok`, sorryAx-free) で既に持つ**。ただし「共通参照測度 `γ` への a.e. rnDeriv
pointwise 収束」ベースで、方針 Y が要する **弱収束 (法則収束)** ベースではない (gap = 弱収束 → a.e. 収束の橋)。
親計画が「klFun-Fatou と向き逆ゆえ方針 X 専用」とした `negMulLog_convDensity_limsup_le` (`:360`) とは別物で、
こちらは **liminf ≥ の正しい向き**。流用見込みは親計画の判定より一段良い (が弱収束橋が残る)。

---

## 主定理の最終形 (再掲) + 方針 Y で剥がす precondition

### 現到達点 (方針 X partial、proof-done)

`entropyPowerExt_add_ge_finite_ac` (`EPIUncondDispatch.lean:88`、proof-done、`#print axioms` sorryAx-free):

```lean
theorem entropyPowerExt_add_ge_finite_ac
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hW_ent : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)
```

### 方針 Y 目標 (剥がすべき precondition)

`hX_ent` / `hY_ent` / `hW_ent` の **3 つの有限微分エントロピー precondition を除去** し、a.c. だが
`h=±∞` (裾の重い / 背の高いピーク密度) 入力でも EPI を成立させる。最終形 (a.c. case のみ抜粋):

```lean
-- 方針 Y a.c. case (達成目標): hX_ent/hY_ent/hW_ent 不要
theorem entropyPowerExt_add_ge_ac_unconditional
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) :
    entropyPowerExt (P.map (X+Y)) ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)
```

証明戦略 (pseudo-Lean、±∞ 場合分け + 弱収束半連続性):

```
by_cases on differentialEntropyExt (P.map X), (P.map Y) ∈ {⊤, ⊥(=h=−∞), finite}:
  -- 0 枝 (どちらか h=−∞, entropyPowerExt = 0):
  N(X)=0 ⟹ RHS = N(Y) ≤ N(X+Y)   -- 拡張単調性 entropyPowerExt_mono_add (W4 自作)
  -- ⊤ 枝 (どちらか h=+∞):
  N(X)=⊤ ⟹ RHS = ⊤  (ℝ≥0∞ で ⊤+x=⊤),  LHS = N(X+Y) = ⊤   -- +∞ 伝播 (W-Y1 自作)
  -- 両 finite 枝:
  両有限微分エントロピー ⟹ entropyPowerExt_add_ge_finite_ac (既存 proof-done) を直接適用
```

**注意**: 両 finite 枝に落ちれば既存 proof-done に帰着するので、方針 Y の追加負荷は ±∞ 枝のみ
(拡張単調性の +∞/−∞ 枝 + +∞ 伝播)。entropy power 弱収束半連続性 (W-Y2) は **a.c. だが有限分散でない**
入力を truncate→smooth→極限で救う層で初めて要る (親計画 §Phase Y step 2)、すなわち def-fix で h=±∞ が
表現可能になった現在でも「EPI 不等式自体が h=±∞ で成立するか」を ±∞ 枝で示す必要があり、その帰結が
W-Y1 (+∞ 伝播) と W-Y2 (有限近似の極限保存) に分かれる。

---

## API 在庫テーブル

凡例: ✅ 既存 (実ファイル Read 確認済) / ❌ 不在 (loogle Found 0 等で確認) / 🔶 in-tree genuine 既存。
file:line は実ファイルを Read で確認した値。Mathlib path は `.lake/packages/mathlib/` 配下。

### A. EReal / ℝ≥0∞ 算術 (拡張単調性 + ±∞ 退化値の lift)

| 概念 | Mathlib API (完全 signature, `[...]` verbatim) | file:line | 状態 | 方針 Y での扱い |
|---|---|---|---|---|
| `EReal.exp` 定義 | `def exp (x : EReal) : ℝ≥0∞ := EReal.rec 0 (fun x => ENNReal.ofReal (Real.exp x)) ∞ x` | `Mathlib/Analysis/SpecialFunctions/Log/ERealExp.lean:40` | ✅ | `entropyPowerExt := EReal.exp (2 * differentialEntropyExt μ)` の核 (型クラス前提なし) |
| `EReal.exp_bot` | `@[simp] lemma exp_bot : exp ⊥ = 0 := rfl` | `…/ERealExp.lean:42` | ✅ | h=−∞ / 特異 → entropyPower 0 (退化値) |
| `EReal.exp_top` | `@[simp] lemma exp_top : exp ⊤ = ∞ := rfl` | `…/ERealExp.lean:44` | ✅ | h=+∞ → entropyPower ⊤ (退化値) |
| `EReal.exp_coe` | `@[simp] lemma exp_coe (x : ℝ) : exp x = ENNReal.ofReal (Real.exp x) := rfl` | `…/ERealExp.lean:45` | ✅ | 有限 a.c. → workhorse 一致 |
| `EReal.exp_monotone` | `@[gcongr] lemma exp_monotone : Monotone exp` | `…/ERealExp.lean:72` | ✅ | **拡張単調性 lift の主役** (`gcongr` 可)。`differentialEntropyExt W ≤ differentialEntropyExt (W+V)` から `entropyPowerExt W ≤ entropyPowerExt (W+V)` |
| `EReal.exp_le_exp_iff` | `@[simp] lemma exp_le_exp_iff {a b : EReal} : exp a ≤ exp b ↔ a ≤ b` | `…/ERealExp.lean:84` | ✅ | 単調性の iff 形 (双方向) |
| ⚠ `EReal.exp_le_exp` | `lemma exp_le_exp {a b : EReal} (h : a ≤ b) : exp a ≤ exp b` | `…/ERealExp.lean:91` | ⚠ **DEPRECATED** (`@[deprecated exp_monotone (since := "2025-10-20")]`) | **使わない** — `exp_monotone` / `exp_le_exp_iff` を使う。親計画 §発見 1 が挙げた `exp_le_exp` は deprecated 化済 |
| `EReal.exp_eq_top_iff` | (`exp a = ⊤ ↔ a = ⊤`、loogle 確認、未 Read) | `…/ERealExp.lean` (要 Read) | ✅ (要 Read) | +∞ 枝判定 |
| `EReal.exp_eq_zero_iff` | (`exp a = 0 ↔ a = ⊥`、loogle 確認、未 Read) | `…/ERealExp.lean` (要 Read) | ✅ (要 Read) | h=−∞ / 特異 枝判定 |
| `EReal.top_sub` | `@[simp] lemma top_sub {x : EReal} (hx : x ≠ ⊤) : ⊤ - x = ⊤` | `Mathlib/Data/EReal/Operations.lean:362` | ✅ | A=⊤,B<⊤ → diffEntExt=⊤ (capstone Case 2 で実使用済) |
| `EReal.sub_top` | `@[simp] theorem sub_top (x : EReal) : x - ⊤ = ⊥` | `…/Operations.lean:343` | ✅ | A<⊤,B=⊤ (h=−∞ ピーク) → diffEntExt=⊥ |
| `EReal.top_sub_bot` | `@[simp] theorem top_sub_bot : (⊤ : EReal) - ⊥ = ⊤` | `…/Operations.lean:347` | ✅ | A=⊤,B=⊥ 端 |
| `EReal.coe_sub` / `EReal.coe_ennreal_toReal` | (有限差 → workhorse 橋、`_of_ac_integrable` 内で実使用) | `Mathlib/Data/EReal/…` | ✅ | bridge `differentialEntropyExt_of_ac_integrable` で既使用 |
| `ENNReal` 加法 `⊤ + x = ⊤` (`top_add` / `add_top`) | (ℝ≥0∞ 標準、loogle 自明) | `Mathlib/Data/ENNReal/…` | ✅ | RHS=⊤ 枝 (片方 h=+∞ ⟹ RHS=⊤) |
| `ENNReal.ofReal_le_ofReal` / `Real.exp_le_exp` | (有限枝 lift、`entropyPowerExt_mixed_add_ge` で実使用済) | `Mathlib/…` | ✅ | 既存 case 2/finite_ac で実使用 |

**結論 A**: 拡張単調性 + ±∞ 退化値の lift に必要な EReal/ℝ≥0∞ 算術は **100% 既存**。唯一の注意は
`exp_le_exp` が deprecated 化済で `exp_monotone` に乗り換えること。`exp_eq_top_iff`/`exp_eq_zero_iff`
の verbatim signature は本調査では Read 未完 (loogle で名前確認のみ) → 「要 Read」マーク。

### B. 条件付けエントロピー機構 (拡張単調性の有限枝 + 混合 case core、既存)

| 概念 | in-tree API (完全 signature, `[...]` verbatim) | file:line | 状態 | 方針 Y での扱い |
|---|---|---|---|---|
| 条件付け微分エントロピー定義 | `noncomputable def condDifferentialEntropy {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsFiniteMeasure μ] : ℝ` | `EPIG2ConvEntropyMonotone.lean:90` | 🔶 genuine | 拡張単調性の有限枝で h(X) ≤ h(X+Y) を供給 |
| **conditioning reduces entropy** | `theorem condDifferentialEntropy_le … : condDifferentialEntropy X Z μ ≤ differentialEntropy (μ.map X)` (型クラス `[MeasurableSpace Ω] [MeasurableSpace α]` + `[IsProbabilityMeasure μ]`、+ **8 integrability precondition** 下記ボックス) | `EPIG2ConvEntropyMonotone.lean:224` | 🔶 genuine `@audit:ok` sorryAx-free | 有限枝 `h(W) ≤ h(W+V)` の核。**±∞ 入力では型 `ℝ` ゆえ使えない** (下記 W-Y1) |
| **independent-sum fibre id** | `theorem condDifferentialEntropy_indep_add_eq {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ) (hX_ac : (μ.map X) ≪ volume) : condDifferentialEntropy (fun ω => X ω + c * Z ω) Z μ = differentialEntropy (μ.map X)` | `EPIG2ConvEntropyMonotone.lean:328` | 🔶 genuine `@audit:ok` sorryAx-free | `h(X+Y|Y) = h(X)`。c=1 で混合 case。同じく型 `ℝ` |
| 混合 case Real 中核 | `theorem differentialEntropy_add_ge_of_indep … : differentialEntropy (P.map X) ≤ differentialEntropy (P.map (fun ω => X ω + Y ω))` (`[IsProbabilityMeasure P]` + 8 integrability) | `EPIUncondMixedCase.lean:76` | 🔶 genuine `@audit:ok` | 有限枝の Real 不等式 (拡張単調性が lift する元) |
| `condDistrib` (Mathlib) | `noncomputable irreducible_def condDistrib {_ : MeasurableSpace α} [MeasurableSpace β] (Y : α → Ω) (X : α → β) (μ : Measure α) [IsFiniteMeasure μ] : Kernel β Ω` (file-level `variable` で **`[StandardBorelSpace Ω] [Nonempty Ω]`** を出力側 `Ω` に要求) | `Mathlib/Probability/Kernel/CondDistrib.lean:64` (型クラス `:54`) | ✅ | **StandardBorel 要求は出力側 `Ω`**。in-tree では出力 = `ℝ` で自動成立。方針 Y も出力は常に `ℝ` ゆえ追加制約なし (Fano inventory の判定と同型) |

**結論 B**: 有限枝 (両 h finite) で要る条件付けエントロピー機構は **全 genuine 既存**。だが
`differentialEntropy : Measure ℝ → ℝ` (Bochner、ℝ 値) ゆえ **h=±∞ を表現できず、±∞ 枝には直接使えない**
(型壁、親計画 判断ログ 5 が指摘した「型衝突」)。拡張単調性の **+∞/−∞ 枝は `differentialEntropyExt : EReal`
レベルで別途組む必要**がある (下記 W-Y1)。

### C. ±∞ 退化値の判定 (h=±∞ a.c. 入力、in-tree)

| 概念 | in-tree API (完全 signature) | file:line | 状態 | 方針 Y での扱い |
|---|---|---|---|---|
| a.c. 枝 raw value | `theorem differentialEntropyExt_of_ac {μ : Measure ℝ} (h : μ ≪ volume) : differentialEntropyExt μ = (((∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume : ℝ≥0∞) : EReal) - ((∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume : ℝ≥0∞) : EReal))` | `EntropyPowerExt.lean:73` | 🔶 genuine `@audit:ok` | a.c. 入力の差 `A − B`。h=+∞ (A=⊤) / h=−∞ (B=⊤) / 有限 を符号判別で出す |
| 有限枝 → workhorse | `theorem differentialEntropyExt_of_ac_integrable {μ : Measure ℝ} (hac : μ ≪ volume) (hint : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) : differentialEntropyExt μ = (differentialEntropy μ : EReal)` | `EntropyPowerExt.lean:89` | 🔶 genuine `@audit:ok` | **有限枝判定の bridge**。`hint` (negMulLog 可積分) が「有限微分エントロピー = 両 finite」を表明。方針 Y は **この `hint` を剥がした版** が要る (= W-Y1 の核) |
| 特異枝 → ⊥ | `theorem differentialEntropyExt_singular {μ : Measure ℝ} (h : ¬ μ ≪ volume) : differentialEntropyExt μ = ⊥` | `EntropyPowerExt.lean:111` | 🔶 genuine `@audit:ok` | 特異判定 |
| entropyPowerExt 有限枝 | `theorem entropyPowerExt_of_ac_integrable {μ : Measure ℝ} (hac : μ ≪ volume) (hint : Integrable (…)) : entropyPowerExt μ = ENNReal.ofReal (Real.exp (2 * differentialEntropy μ))` | `EntropyPowerExt.lean:118` | 🔶 genuine `@audit:ok` | 有限 a.c. の ℝ≥0∞ 値 |
| **+∞ → ⊤ bridge** | `theorem entropyPowerExt_eq_top_of_diffEntExt_top {μ : Measure ℝ} (h : differentialEntropyExt μ = ⊤) : entropyPowerExt μ = ⊤` | `EntropyPowerExt.lean:129` | 🔶 genuine `@audit:ok` | **h=+∞ → entropyPower ⊤**。+∞ 枝で `le_top` を出すための既存 bridge。**W-Y1 の +∞ 伝播の出口** |
| 特異/−∞ → 0 | `theorem entropyPowerExt_singular {μ : Measure ℝ} (h : ¬ μ ≪ volume) : entropyPowerExt μ = 0` | `EntropyPowerExt.lean:136` | 🔶 genuine `@audit:ok` | 特異枝 (h=−∞ a.c. は別、A<⊤ B=⊤ で diffEntExt=⊥ → exp⊥=0) |
| 無限分散 a.c. EPI (両有限エントロピー) | `theorem entropyPowerExt_add_ge_infinite_variance (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX hY : Measurable) (hXY : IndepFun X Y P) (hX_ac hY_ac : ≪ volume) (hX_ent hY_ent : Integrable (negMulLog ∘ density) volume) (h_infvar : ¬(2次moment X ∧ 2次moment Y)) : entropyPowerExt (P.map (X+Y)) ≥ N(X)+N(Y)` | `EPIInfiniteVarianceCapstone.lean:323` | 🔶 genuine `@audit:ok` sorryAx-free | **方針 Y で剥がす対象**: `hX_ent`/`hY_ent` を持つ。これらを ±∞ 枝で除去するのが方針 Y |

**結論 C**: h=±∞ a.c. 入力の **判定・退化値 lemma は完備**。差 `A − B` の符号で +∞ (A=⊤)/−∞ (B=⊤)/有限を
出す機構 (`differentialEntropyExt_of_ac` + `entropyPowerExt_eq_top_of_diffEntExt_top`) が既に genuine。
**欠けているのは「+∞ が独立和で伝播する」推論 (W-Y1) と「弱収束で値が保たれる」半連続性 (W-Y2) のみ**。

### D. Fatou / 半連続性 / 弱収束 (W-Y2 = entropy power 弱収束半連続性の素材)

| 概念 | API (完全 signature, `[...]` verbatim) | file:line | 状態 | 方針 Y での扱い |
|---|---|---|---|---|
| **Fatou (lintegral liminf)** | `theorem lintegral_liminf_le {ι : Type*} {f : ι → α → ℝ≥0∞} {u : Filter ι} [IsCountablyGenerated u] (h_meas : ∀ i, Measurable (f i)) : ∫⁻ a, liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) u` | `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:231` | ✅ | LSC の数学的核 (in-tree `klDiv_le_liminf_of_ae_tendsto` が既使用) |
| **portmanteau open-set LSC** | `lemma lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure {μ : Measure Ω} {μs : ℕ → Measure Ω} {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f) (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i))` (型クラス `[MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]`) | `Mathlib/MeasureTheory/Measure/Portmanteau.lean:496` | ✅ | **弱収束 → lintegral LSC の Mathlib 素材**。⚠ **`f_nn : 0 ≤ f` (非負) + `f_cont : Continuous f` を要求** → `negMulLog (density)` (符号変化・非連続) には直接使えない、構造のみ |
| **in-tree KL liminf LSC (genuine!)** | `theorem klDiv_le_liminf_of_ae_tendsto (γ : Measure ℝ) [IsFiniteMeasure γ] (μ : Measure ℝ) (μ_n : ℕ → Measure ℝ) [IsFiniteMeasure μ] [∀ n, IsFiniteMeasure (μ_n n)] (hμ_ac : μ ≪ γ) (hμn_ac : ∀ n, μ_n n ≪ γ) (h_ae : ∀ᵐ x ∂γ, Tendsto (fun n => ((μ_n n).rnDeriv γ x).toReal) atTop (𝓝 ((μ.rnDeriv γ x).toReal))) : klDiv μ γ ≤ Filter.liminf (fun n => klDiv (μ_n n) γ) atTop` | `EPIG2KLFatouLSC.lean:112` | 🔶 genuine `@audit:ok` | **方針 Y W-Y2 の最有力流用候補**。liminf ≥ の正しい向き。**gap = 「共通参照 `γ` への a.e. rnDeriv 収束」前提で、弱収束 (法則収束) ではない** → 弱収束 → a.e. rnDeriv 収束の橋が要る |
| in-tree limsup (向き逆、方針 X 専用) | `theorem negMulLog_convDensity_limsup_le {pX : ℝ → ℝ} (hpX_nn …) (hpX_meas …) (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1) (hpX_mom : Integrable (fun y => y^2 * pX y) volume) (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume) {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (u …) (hu_lim …) : Filter.limsup (…) atTop ≤ ∫ x, Real.negMulLog (pX x) ∂volume` | `EPIG2KLFatouLSC.lean:360` | 🔶 genuine `@audit:ok` | **方針 Y には使えない** (limsup ≤ で向き逆、かつ `hpX_mom` 有限分散 + `hpX_ent` 有限エントロピー precondition 持ち = 方針 X 専用)。親計画 §S5 verdict と一致 |
| Gaussian 弱収束 (approx identity) | — | — | ❌ **不在** (loogle `ProbabilityTheory.gaussianReal, Filter.Tendsto` = **Found 0**) | `gaussianReal 0 t → dirac 0` (t→0) の弱収束。**W-Y2 の前提、Mathlib 完全不在** |

**結論 D**: Fatou / portmanteau LSC は存在し、**in-tree `klDiv_le_liminf_of_ae_tendsto` が KL の liminf
半連続性を genuine に既に持つ** (親計画の「klFun-Fatou と向き逆ゆえ方針 X 専用」判定は `limsup_le` 側を
指しており、`liminf` 側はむしろ方針 Y の正しい向き)。**ただし「弱収束」ベースではなく「共通参照 γ への
a.e. rnDeriv 収束」ベース**で、方針 Y の truncate→smooth→極限が生む収束がこの形に乗るかが gap。
Gaussian 弱収束 (approximation identity) は **Mathlib 完全不在** (W-Y2 の真の壁部分)。

---

## 主要前提条件ボックス (事故が起きやすい lemma)

### `condDifferentialEntropy_le` (`EPIG2ConvEntropyMonotone.lean:224`) — 8 integrability precondition

型クラス: `{Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]` + `[IsProbabilityMeasure μ]`。
以下 8 本 (verbatim、`X := X` `Z := Z` `μ := μ`):

- `hX : Measurable X`、`hZ : Measurable Z`、`hX_ac : (μ.map X) ≪ volume` (regularity、3 本)
- `h_ac : (μ.map Z) ⊗ₘ condDistrib X Z μ ≪ (μ.map Z) ⊗ₘ Kernel.const α (μ.map X)` (joint a.c.)
- `h_int : Integrable (llr (joint) (product)) (joint)` (joint llr 可積分)
- `hκ_v : ∀ᵐ z ∂(μ.map Z), condDistrib X Z μ z ≪ volume` (per-fibre a.c.)
- `hκ_logp_int`, `hκ_cross_int` : per-fibre log-density / cross 可積分 (∀ᵐ z)
- `h_fibreEnt_int : Integrable (fun z => differentialEntropy (condDistrib X Z μ z)) (μ.map Z)` (outer fibre entropy 可積分)
- `h_cross_int`, `h_logq_int` : outer cross / marginal log-density 可積分

**8 前提のうち a.c. のみから R-N で自動 follow するもの / 追加 regularity の区別** (方針 Y 重要):

- **a.c. から自動 (R-N で)**: `hκ_v` (joint a.c. ⟹ per-fibre a.c.、`absolutelyContinuous_compProd_right_iff` で本体内で導出済、`:159-163`)、`h_ac` (両 a.c. + 独立から joint a.c.)。
- **本質的に有限エントロピー / 有限性を要求 (a.c. だけでは出ない)**: `h_int` (joint llr 可積分 = KL 有限性)、`h_fibreEnt_int` (fibre entropy が μ_Z 可積分 = 各 fibre の h が有限かつ平均可積分)、`hκ_logp_int`/`hκ_cross_int`/`h_cross_int`/`h_logq_int` (log-density 可積分性)。**これらが `hX_ent`/`hW_ent` (有限微分エントロピー) と同階層の "h finite" 前提**で、方針 Y が剥がしたい対象。

→ **判定**: `condDifferentialEntropy_le` は **型 `ℝ` ゆえ h=±∞ 枝には端から使えない** (型壁)。方針 Y の
有限枝 (両 h finite) のみで使い、±∞ 枝は `differentialEntropyExt : EReal` レベルで別機構 (W-Y1) を組む。

### `differentialEntropyExt_of_ac_integrable` (`EntropyPowerExt.lean:89`) — `hint` の意味

- `hint : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume` は **"両 finite" (A,B 共に有限) を表明する regularity precondition**。これがあると workhorse `differentialEntropy` に一致 (有限枝)。
- 方針 Y は `hint` 無しで `differentialEntropyExt_of_ac` (raw 差 `A − B`) から直接 +∞ (A=⊤) / −∞ (B=⊤) を扱う。capstone Case 2 (`:344-`) が「`¬ hint` + `B<⊤` から `A=⊤`」を導く実例を既に持つ — 単独測度に対しては動く。**方針 Y で新しいのは「独立和で `A=⊤` が伝播する」推論** (W-Y1)。

### portmanteau LSC (`Portmanteau.lean:496`) — 非負・連続前提

- `f_nn : 0 ≤ f` + `f_cont : Continuous f` を **両方**要求。`negMulLog (density)` は符号変化 (density>1 で負) かつ density 経由で非連続ゆえ **直接適用不可**。truncation / 正部負部分解で非負連続部に落とす前処理が要る (in-tree `klDiv_le_liminf_of_ae_tendsto` は `klFun ≥ 0` の非負性を使って Fatou 直行ルートを取り portmanteau を回避している — そちらが流用本線)。

---

## 自作が必要な要素 (優先度順)

### 1. (W-Y1) 拡張エントロピー単調性 `entropyPowerExt_mono_add` ★最優先

- **signature (推奨、def-fix plan §2 P2 由来)**:
  `W a.c. ∧ V indep ⟹ entropyPowerExt (P.map (W+V)) ≥ entropyPowerExt (P.map W)`
- **3 枝構成**:
  - **−∞ 枝** (`differentialEntropyExt (P.map W) = ⊥`): `entropyPowerExt (P.map W) = exp ⊥ = 0`、`bot_le` / `zero_le'`。**genuine、~5 行**。
  - **有限枝** (両 a.c.+integrable): 既存 `differentialEntropy_add_ge_of_indep` (`EPIUncondMixedCase.lean:76`、8 integrability honest precondition) を `EReal.exp_monotone` + `entropyPowerExt_of_ac_integrable` で lift。**genuine、~20 行** (`entropyPowerExt_mixed_add_ge` が雛形)。
  - **+∞ 枝** (`differentialEntropyExt (P.map W) = ⊤`): `entropyPowerExt (P.map W) = ⊤`、要 `entropyPowerExt (P.map (W+V)) = ⊤` = **+∞ 伝播** `h(W)=+∞ ∧ V indep ⟹ h(W+V)=+∞`。これが核心の自作。
- **+∞ 伝播の数学**: h(W)=+∞ (正部発散 = W が裾の重い密度) のとき W+V も裾が残る (V との畳み込みは裾を消さない、親計画 §S5 verdict step 1 と同じ理由)。よって A(W+V)=∫⁻ ofReal(negMulLog density(W+V)) = ⊤。**Mathlib 壁ではなく extended-entropy plumbing** (親 def-fix plan §2 判定)。
- **工数感**: −∞/有限枝 ~25 行 (既存資産流用)。+∞ 伝播 ~80-150 行 (畳み込みが裾を保つ lintegral 評価。`condDifferentialEntropy_le` の +∞ 版を EReal で組むか、density 直接評価)。**def-fix plan で `plan:epi-uncond-deffix-monotone-plan` slug 予約済 (wall でない)**。
- **落とし穴**: 型 `ℝ` の `condDifferentialEntropy_le` は +∞ 枝で使えない (型壁)。+∞ 伝播は `differentialEntropyExt : EReal` か lintegral レベルで新規に組む。density(W+V) = convDensityAdd / conv の裾評価が要る。

### 2. (W-Y2) entropy power 弱収束半連続性 — a.c. だが有限分散でない入力を救う層

- **必要性**: ±∞ 枝 (W-Y1) は「h=±∞ a.c. 入力」を扱うが、**「有限 h だが無限分散」入力** (例 Cauchy) は h finite なので両 finite 枝に落ちる。実は **無限分散 a.c. は既に route T (capstone) で closure 済** (有限エントロピー前提下)。すなわち W-Y2 が真に要るのは **「有限エントロピーすら無いが a.c.」を有限分散+有限エントロピー入力で近似する極限保存** = 方針 Y のうち W-Y1 で扱えない残部。
- **推奨**: in-tree `klDiv_le_liminf_of_ae_tendsto` (`:112`) を流用。entropy = −KL(μ‖volume) 風の Fatou-liminf 形で `differentialEntropyExt (lim) ≤ liminf differentialEntropyExt (近似列)` (or 適切な向き)。
- **gap**: 弱収束 (法則収束、truncate→smooth の極限) → 「共通参照 γ への a.e. rnDeriv 収束」の橋。Gaussian 弱収束 approximation identity (loogle Found 0) を含む。**200-400 行 (Mathlib 壁含む)**。
- **判定**: route T が無限分散 (有限エントロピー) を既に閉じたため、W-Y2 の負荷は親計画 §S5 verdict 時点より縮小。ただし依然 Gaussian 弱収束が Mathlib 不在の壁。

### 3. (補助) 拡張単調性で要る a.c. 保存 — 既存

- `map_add_absolutelyContinuous` (`EPIUncondMixedCase.lean:55`、genuine `@audit:ok`): `X a.c. ∧ X⊥Y ⟹ X+Y a.c.`。W-Y1 の有限/±∞ 枝で W+V の a.c. を供給。**自作不要、既存**。

---

## Mathlib 壁の列挙 (真の不在、`@residual(wall:<slug>)` 対象)

| wall slug | 主張 | loogle 確認 (query → 結果) | shared sorry 補題化 |
|---|---|---|---|
| `epi-entropy-lsc-weak` (親計画 §S5 既登録 `wall:entropy-lsc-weak`) | entropy / KL の **弱収束** 下半連続性 `X_t → X (法則) ⟹ liminf N(X_t) ≥ N(X)` | `"klDiv", LowerSemicontinuous` → **Found 67 LSC 宣言中 klDiv 名 0**。`MeasureTheory.klDiv, LowerSemicontinuous` → unknown ident (klDiv は ProbabilityTheory namespace) | **集約推奨** (W-Y2 の核、複数 family 不要だが in-tree LSC `klDiv_le_liminf_of_ae_tendsto` の弱収束版として 1 本に) |
| `gaussian-approx-identity-weak` (親計画 §S5 既登録) | `gaussianReal 0 t → dirac 0` (t→0) の弱収束 (approximation identity) | `ProbabilityTheory.gaussianReal, Filter.Tendsto` → **Found 0** | shared sorry 候補 (W-Y2 前提) |

**注**: W-Y1 (+∞ 伝播) は **wall ではなく `plan:epi-uncond-deffix-monotone-plan`** (extended-entropy plumbing、
def-fix plan §2/§4 P2 が明示。conv が裾を保つ lintegral 評価で genuine closeable、gateway atom 不在ではない)。
親計画 判断ログ 5 が「entropyPowerExt の def-fix で h=±∞ は表現可能になったが EPI 不等式自体の h=±∞ 成立性は
別検討」とした部分が、本調査で **W-Y1 (plan-closeable plumbing) と W-Y2 (genuine weak-LSC wall) に分離**。

---

## 撤退ラインへの距離

親計画の撤退ライン **L-Uncond-3-scope** (`epi-unconditional-moonshot-plan.md:97`):
> 「方針 Y が semicontinuity wall で genuine に詰まったら、有限分散+有限エントロピーを honest precondition
> として残す方針 X に縮退して着地」

### 判定: **発動しない (が ROI 判断は別)**

- **発動条件 = 「semicontinuity wall で genuine に詰まる」** だが、本調査で **W-Y2 (entropy 弱収束 LSC) は
  完全に詰まってはいない**: in-tree `klDiv_le_liminf_of_ae_tendsto` が liminf 半連続性を genuine に持ち
  (正しい向き)、残るは「弱収束 → a.e. rnDeriv 収束」の橋 + Gaussian approximation identity の 2 部品。
  後者は loogle Found 0 (真の Mathlib 不在) だが、これは **gateway atom 不在ではなく plumbing + 1 壁**。
- **W-Y1 (+∞ 伝播) は wall ですらない** (plan-closeable plumbing)。
- ⇒ **方針 Y は数学的に true かつ gateway atom が存在する** (CLAUDE.md「family 丸ごと壁と断じる前に
  gateway atom を試す」基準で、`entropyPowerExt_mono_add` の −∞/有限枝は即実装可能 = gateway 通過)。
  したがって L-Uncond-3-scope の **「genuine に詰まる」は満たさない**。

### ただし ROI 縮退の余地 (新規撤退ライン提案)

完全無条件 (方針 Y) の残作業は W-Y1 (~80-150 行 plumbing) + W-Y2 (~200-400 行、Gaussian 弱収束 wall 含む)。
現到達点 (`entropyPowerExt_add_ge_finite_ac`、proof-done) は **a.c.+有限エントロピーで既に方針 X より強い**
(有限分散 precondition は route T で外れた)。よって:

- **新規撤退ライン L-Uncond-Y-roi 提案** (本調査由来、honest 後退口): W-Y1 の +∞ 伝播が 1 session で
  closeable なら **±∞ 枝まで剥がした「a.c. 無条件 (有限エントロピー precondition 不要)」を中間到達点**とし、
  W-Y2 (Gaussian 弱収束 wall = 有限エントロピーすら無い a.c. の極限近似) を `sorry +
  @residual(wall:gaussian-approx-identity-weak)` で park。これは方針 X (有限分散残置) より strictly 強い
  honest 中間形で、撤退ではなく **段階的前進**。signature は結論形を保ち仮説束化しない。

---

## 着手 skeleton (W-Y1 拡張単調性、~25 行)

`InformationTheory/Shannon/EPIUncondExtMonotone.lean` (新規) の出だし:

```lean
import InformationTheory.Shannon.EntropyPowerExt
import InformationTheory.Shannon.EPIUncondMixedCase
import InformationTheory.Shannon.EPIG2ConvEntropyMonotone
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.MeasureTheory.Group.Convolution

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **+∞ 伝播** (W-Y1 核): `h(W) = +∞ ∧ W ⊥ V ⟹ h(W+V) = +∞`。
畳み込みが裾 (正部発散) を保つことから。extended-entropy plumbing (Mathlib 壁でない)。 -/
theorem differentialEntropyExt_top_of_indep_add
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    differentialEntropyExt (P.map (fun ω => W ω + V ω)) = ⊤ := by
  sorry -- @residual(plan:epi-uncond-deffix-monotone-plan)

/-- **拡張エントロピー単調性** (W-Y1): `W a.c. ∧ W ⊥ V ⟹ N(W+V) ≥ N(W)`。
−∞ 枝 `bot_le` / 有限枝 lift (`differentialEntropy_add_ge_of_indep` + `EReal.exp_monotone`) /
+∞ 枝 (`differentialEntropyExt_top_of_indep_add` + `entropyPowerExt_eq_top_of_diffEntExt_top` + `le_top`)。 -/
theorem entropyPowerExt_mono_add
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume) :
    entropyPowerExt (P.map (fun ω => W ω + V ω)) ≥ entropyPowerExt (P.map W) := by
  sorry -- @residual(plan:epi-uncond-deffix-monotone-plan)

end InformationTheory.Shannon
```

着手後 1 つ目の `sorry` (`differentialEntropyExt_top_of_indep_add`) を「W+V density の正部 lintegral が
W の正部発散から ⊤ を継ぐ」形で割っていくのが W-Y1-M1。`hV` (V の measurability)・`hWV` (独立) は
W+V の a.c. (`map_add_absolutelyContinuous`) と density 形に使う honest precondition。

---

## consumer footprint (signature 変更時の ripple)

`entropyPowerExt_add_ge_finite_ac` (`EPIUncondDispatch.lean:88`) / `_dispatch_skeleton` (`:145`) を
方針 Y で precondition 削減 (`hX_ent`/`hY_ent`/`hW_ent` 除去) する場合の direct consumer は
**`EPIUncondDispatch.lean` 内に閉じる** (`rg -l` で外部 file なし)。`entropyPowerExt_add_ge_infinite_variance`
(capstone `:323`) の consumer も `EPIUncondDispatch.lean:105` の 1 箇所のみ。

→ **ripple は EPI uncond cluster 内に局所化**、blast radius 小。precondition を緩める (削除) 方向ゆえ
consumer 側は引数を渡さなくなるだけで型は保たれる (緩和は consumer を壊さない)。
※ `dep_consumers.sh` の term レベル実値は root olean warm 前提で未実行 (本調査は read-only)。実装着手時に
`scripts/dep_consumers.sh InformationTheory.Shannon.entropyPowerExt_add_ge_finite_ac` で再確認推奨。

---

## まとめ

- **既存率**: 方針 Y で使う API のうち実体は **~85% 既存** (EReal 算術 / 条件付けエントロピー機構 /
  ±∞ 判定 / Fatou-LSC の in-tree 実績はすべて揃う)。自作必要は **2 件** (W-Y1 拡張単調性の +∞ 伝播 =
  plan-closeable、W-Y2 entropy 弱収束 LSC = genuine wall 含む)。
- **撤退ライン**: L-Uncond-3-scope は **発動しない** (gateway atom = `entropyPowerExt_mono_add` の
  −∞/有限枝が即実装可能、方針 Y は数学的 true)。ただし ROI 縮退の中間到達点として新規
  L-Uncond-Y-roi (a.c. 無条件中間形 + W-Y2 park) を提案。
- **最も危険な発見**: 親計画 §S5 が「流用候補 `negMulLog_convDensity_limsup_le` は limsup ≤ で向き逆」と
  したのは正しいが、**別の in-tree lemma `klDiv_le_liminf_of_ae_tendsto` (`:112`) が liminf ≥ の正しい
  向きで genuine 既存**だった (KL Fatou-LSC)。これにより W-Y2 の核は「ゼロから自作」でなく「弱収束 →
  a.e. rnDeriv 収束の橋 + Gaussian approximation identity」に縮小する。ただし後者は loogle Found 0 の
  真の Mathlib 壁。
</content>

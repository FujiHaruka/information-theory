# 無条件 EPI — entropyPowerExt def-fix + 拡張単調性 campaign

> **親**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) (傘 moonshot)。本 plan は傘の **Phase 1 (S1 retype) の defect 訂正 + Phase 5 dispatch 再構成** を担う。
> **slug**: `epi-uncond-deffix-monotone-plan`。
> **status**: 2026-06-06 起草 (def-fix campaign P1-P5 done)。**2026-06-07 更新**: W-Y1 gateway atom 着手 + machine 再評価で +∞ 伝播の攻略を §7 に再設計 (route α = EReal-conditioning primary、当初「plumbing」見積り訂正、multi-session moonshot 規模)。次 session で §7 着手。

## 0. 発見 (機械検証済、linchpin)

真の無条件 headline = `entropyPowerExt_add_ge_dispatch_skeleton` (`EPIUncondMixedCase.lean:234`、ℝ≥0∞、h_stam 無し)。唯一の残 sorry = case 1 (両 a.c.) @ `:289`。

**この case-1 obligation は現 def の下で FALSE-as-stated** (機械検証、`/tmp/test_garbage.lean`):
- 現 `entropyPowerExt` a.c. 枝 (`EntropyPowerExt.lean:56` `entropyPowerExt_of_ac`) = `ofReal(exp(2·differentialEntropy μ))`、**常に有限**。
- `differentialEntropy` (`DifferentialEntropy.lean:45`) は Bochner 積分 → `negMulLog(density)` 非可積分時 **0 を返す** (`MeasureTheory.integral_undef`)。
- ⇒ **無限エントロピー a.c.** 入力 (密度 ∝ 1/(x log²x)、有限質量だが h=+∞) で `entropyPowerExt = ofReal(exp 0) = 1` (garbage)。Gaussian Y (entropyPowerExt≈5.4) と組むと case-1 主張 `1 ≥ 1+5.4` は**偽**。
- 同様に **h=−∞** a.c. 入力 (密度に背の高いピーク、∫ f log f = +∞) でも garbage 1 を返し偽。

→ case-1 sorry は「埋めれば偽命題を証明する」状態。`@residual(plan:...)` 分類は誤り (実は false-statement)。**def 修正が無条件 EPI 健全性の linchpin**。

## 1. 訂正 def 設計 (validated prototype、`/tmp/epi_deffix_proto.lean` compiles)

⚠ **recon synthesis の素朴案「非可積分 → ⊤」は誤り** (h=−∞ 密度を ∞ に飛ばし別の false-statement を作る)。非可積分には h=+∞ (裾) と h=−∞ (ピーク) の両方があり、符号で判別必須。

正しい設計 = **正部・負部の EReal 差**:

```lean
open Classical in
noncomputable irreducible_def differentialEntropyExt (μ : Measure ℝ) : EReal :=
  if μ ≪ volume then
    (((∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume : ℝ≥0∞) : EReal)
      - ((∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume : ℝ≥0∞) : EReal))
  else ⊥
```

`A := ∫⁻ ofReal(negMulLog f)` (正部), `B := ∫⁻ ofReal(-negMulLog f)` (負部)。EReal 差 `(A:EReal) - (B:EReal)`:
- A,B 共に有限 (= integrable) → workhorse `differentialEntropy` に一致 (bridge、下記)。
- A=⊤, B<⊤ (正部発散=裾) → ⊤ ⇒ `entropyPowerExt = exp ⊤ = ∞`。**h=+∞ 正しく ∞**。
- A<⊤, B=⊤ (負部発散=ピーク) → `fin - ⊤ = ⊥` ⇒ `exp ⊥ = 0`。**h=−∞ 正しく 0**。
- A=⊤, B=⊤ (両発散) → `⊤ - ⊤ = ⊥` (EReal) ⇒ 0 (safe; entropy undefined を 0 に倒すのは EPI に安全 = RHS 縮小)。

`entropyPowerExt := EReal.exp (2 * differentialEntropyExt μ)` は**不変** (`EReal.exp` が exp⊤=∞ / exp⊥=0 / exp↑x=ofReal を吸収)。修正は differentialEntropyExt の a.c. 枝のみ。

**bridge (validated)**: `differentialEntropyExt_of_ac_integrable (hac) (hint : Integrable (negMulLog∘dens) volume) : differentialEntropyExt μ = (differentialEntropy μ : EReal)` を `MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part` (Bochner = toReal A − toReal B) + `EReal.coe_sub` + `EReal.coe_ennreal_toReal` で証明 (prototype 済)。正部/負部有限性は `Integrable.hasFiniteIntegral` + `ofReal(g) ≤ ‖g‖ₑ` の lintegral_mono。

## 2. アーキ (monotonicity-centric)

def 修正は case-2 (mixed) を破る (`entropyPowerExt_mixed_add_ge:165` が `entropyPowerExt_of_ac` で ofReal lift → 有限 entropy 限定に)。case-2 statement は真のまま (monotonicity で出る) だが proof を一般化要。**中心補題 = 拡張単調性**:

**`entropyPowerExt_mono_add`**: W a.c.、V 独立 ⟹ `entropyPowerExt (P.map (W+V)) ≥ entropyPowerExt (P.map W)`。
(W+V a.c. は `map_add_absolutelyContinuous` (`EPIUncondMixedCase.lean:55`) で W a.c. から。`EReal.exp` 単調 ← `differentialEntropyExt(W) ≤ differentialEntropyExt(W+V)`。)
- **−∞ 枝** (diffEntExt W = ⊥): `bot_le`。genuine。
- **有限枝** (a.c.+integrable): 既存 Real `differentialEntropy_add_ge_of_indep` (`EPIUncondMixedCase.lean:76`、8 integrability honest precondition) を bridge で lift。genuine。
- **+∞ 枝** (diffEntExt W = ⊤): diffEntExt(W+V)=⊤ 要 (+∞ 伝播)。**⚠ 2026-06-07 machine 再評価で「plumbing ~80-150 行」は過小評価と判明 → 攻略は §7 が SoT** (route α = EReal-conditioning が本筋、A/B 分解は回避可)。`sorry + @residual(plan:epi-uncond-deffix-monotone-plan)`。

これで:
- **case-2 (X a.c., Y 特異)**: RHS = N(X)+0 = N(X) ≤ N(X+Y) (mono)。全 entropy 値で genuine (+∞ 枝が閉じれば)。
- **case-3 (両特異)**: 不変 genuine。
- **case-1 両 a.c.**: sub-case 分岐:
  - X か Y が +∞ entropy: RHS=⊤ (ℝ≥0∞ で ⊤+x=⊤)、LHS=⊤ (mono)。
  - X か Y が 0 (h=−∞): その項 0、RHS=他項 ≤ N(X+Y) (mono)。
  - 両有限 entropy: **classical EPI** (下記 §3)。

## 3. case-1 両有限 entropy = classical EPI (残 core)

両 a.c. + 両有限 entropy の `N(X+Y) ≥ N(X)+N(Y)` (= 古典 EPI、mono では出ない、和が要る)。
- Phase A `entropy_power_inequality_of_density` (`EPIDensityForm.lean:70`、sorryAx-free) は **正則密度** (IsRegularDensityV2 等 16 precondition) のみ。一般有限 entropy a.c. には直接適用不可。
- 一般有限分散 a.c. → smoothing で正則化 + endpoint 連続性 (`heatFlowEntropyPower_continuousWithinAt_zero`、有限分散+有限 entropy 要) = 方針 X (`epi-case1-difference-g3-closure-plan`、partial)。
- 無限分散 a.c. = **genuine Mathlib 壁** (Lieb-Young 不在、recon thread D で再確認)。

→ case-1 両有限 entropy は本 session では **named wall `wall:epi-finite-entropy-ac-classical`** に隔離 (Phase A は正則枝の genuine discharge、一般枝は wall)。後続で方針 X (有限分散) を method-X closure、無限分散を別 moonshot。

## 4. 実装 campaign (Phase)

- [x] **P1 def-fix** ✅ (`EntropyPowerExt.lean`、2026-06-06): 訂正 def (正部・負部 EReal 差) + `differentialEntropyExt_of_ac` (raw) + `_of_ac_integrable` (bridge、`integral_eq_lintegral_pos_part_sub_lintegral_neg_part` 経由) + `entropyPowerExt_of_ac_integrable` + `entropyPowerExt_eq_top_of_diffEntExt_top` (+∞→∞) + 特異枝不変 + sanity gate `_gaussianReal` を `integrable_negMulLog_gaussianReal_density` (新 helper、`memLp_id_gaussianReal` + `integrable_withDensity_iff`) で修復。**全 sorryAx-free** (`#print axioms` `[propext, Classical.choice, Quot.sound]`)。
- [~] **P2 拡張単調性** `entropyPowerExt_mono_add` (`EPIUncondMonotone.lean:135`、2026-06-07 gateway atom 着手済) — **−∞ 枝 + EReal lift genuine、+∞ 伝播 (`:77`) + 有限枝 (`:120`) は sorry** (`@residual(plan:epi-uncond-deffix-monotone-plan)`、独立監査 PASS)。**+∞ 伝播の攻略は §7 が SoT** (route α = EReal-conditioning 本筋、multi-session moonshot 規模、当初「plumbing」見積りは machine 再評価で訂正)。
- [x] **P3 dispatch 再構成** ✅ (`EPIUncondMixedCase.lean`、2026-06-06): case-2 `entropyPowerExt_mixed_add_ge` (+ symm) に finite-entropy 前提 `hX_ent`/`hW_ent` 追加 + `_of_ac_integrable` 使用 (genuine 維持)。case-1 の **false-as-stated だった bare sorry を named wall `entropyPowerExt_add_ge_finite_ac` (`@residual(wall:epi-finite-entropy-ac-classical)`) に置換**。dispatch は finite-entropy 4 前提を thread (方針 X partial scope)。**case-2/3/symm sorryAx-free 維持、唯一の sorry = named wall 1 本**。
- [x] **P4 独立 honesty-auditor** ✅ (2026-06-06): 13 declaration 監査 = 11 ok / 1 honest_residual (named wall) / 1 dispatch transitive sorry / **0 defect**。訂正 def の退化非悪用 (±∞ 正写像) 機械検証、finite-entropy 前提の non-load-bearing 確認、`wall:epi-finite-entropy-ac-classical` 分類妥当性 (一般 a.c. 無限分散 = Lieb-Young 不在 loogle Found 0) を独立確認。`@audit:ok` 付与済。
- [x] **P5 wall register 登録 + commit** ✅: `audit-tags.md` Wall name register に `epi-finite-entropy-ac-classical` 追記。

### 到達点 (本 session、2026-06-06)
**無条件 headline `entropyPowerExt_add_ge_dispatch_skeleton` は def-fix で TRUE-as-stated 化、唯一の sorry = `wall:epi-finite-entropy-ac-classical` (両 a.c. 有限エントロピー古典 EPI) 1 本に局所化。** 旧状態「false-as-stated monolithic sorry」→「sound + 精密 named wall 1 本」へ昇格。残: (a) named wall closure (正則=Phase A 済、有限分散=方針 X、無限分散=genuine 壁)、(b) infinite-entropy 入力の precondition 撤去 (+∞ 伝播 = P2)。

## 5. 撤退ライン

- **P1 def-fix が downstream を大量破壊**: case-2 を mono 化する前に EntropyPowerExt 単体を clean にし、`_of_ac` 利用箇所 (sanity gate / case-2) を順に修復。詰まれば `entropyPowerExt_of_ac_integrable` に finite-entropy precondition を honest に追加 (load-bearing でない)。
- **P2 +∞ 伝播が今 session 不可**: `sorry + @residual(plan:epi-uncond-deffix-monotone-plan)` で park (wall でなく plan、後続 closeable)。case-1b 無限 entropy 枝も同 residual 経由 (mono に乗る)。
- **共通**: 詰まったら signature を結論形に保ち `sorry + @residual`。`*Hypothesis` bundle / 退化定義悪用 / 名前ロンダリング禁止。`_unconditional` 命名は threaded integrability precondition が残る間は name-laundering ゆえ不可 (傘 Phase 5 判断ログ 2 と整合)。

## 6. honest 到達点 (2026-06-06 session target)

headline TRUE-as-stated (def-fix)。genuine close: singular/mixed/(−∞ or 0 entropy)/(+∞ entropy if 伝播閉)。残 named wall: (a) +∞ 伝播 (閉じなければ、plan slug)、(b) `wall:epi-finite-entropy-ac-classical` (両有限 entropy 一般 a.c. の古典 EPI、方針 X partial + 無限分散 wall)。**現状の「false-as-stated monolithic sorry」から「true-as-stated + 精密 named wall 1-2 本」への昇格が成果**。

---

## 7. W-Y1 (+∞ 伝播 / 拡張単調性) 攻略計画 — 2026-06-07 machine 再評価

> §2/§4 P2 の「+∞ 伝播 = extended-entropy plumbing ~80-150 行、Mathlib 壁でない」は **過小評価**だった。
> 本節が SoT。gateway atom `entropyPowerExt_mono_add` (`EPIUncondMonotone.lean:135`、新規 file) と
> +∞ 伝播 `differentialEntropyExt_top_of_indep_add` (`:77`) の 2 sorry を closure する攻略。
> ユーザー確認 (2026-06-07): 大ゴール (方針 Y 完全無条件) 不変、次 session で壁に挑む。

### 7-0. machine 再評価の結論 (loogle conclusion-shape 二段 + verbatim signature)

+∞ 伝播 `h(W)=⊤ ⟹ h(W+V)=⊤` を「A_{W+V}=⊤ ∧ B_{W+V}<⊤」の 2 obligation に割ると、**両方とも当初見積りより重い**:

- **Mathlib の Jensen は全て `Integrable (g∘f)` 要求** (verbatim、`ConvexOn.map_integral_le`
  `Mathlib/Analysis/Convex/Integral.lean:199`、`map_average_le:130`)。「φ 下に有界 → RHS +∞ 許容」版は不在。
  ⇒ capstone 補題1 `integrable_negPart_negMulLog_map_sum` (`EPIInfiniteVarianceCapstone.lean:74`) の
  Jensen block (L220-273) は **片成分の完全有限エントロピー** (A も B も有限) を要求し、⊤ 枝 (A_W=⊤) では呼べない。
- `Measure.conv` の entropy-monotone: loogle `"…conv", \|- _ ≤ _` **Found 0**。conv の essSup peak bound **Found 0**。
  lintegral/ℝ≥0∞ Jensen **Found 0**。in-tree `negMulLog_convDensity_entropy_ge_density`
  (`EPIG2ConvEntropyDensity.lean:124`) は有限分散+有限エントロピー必須 (h=±∞ 不適用)。
- proof-pivot-advisor の「enorm 分解で A=⊤」案は **循環**: B<⊤ 下で「和エントロピー非可積分」≡「A_{W+V}=⊤」。
  capstone Case 2 (`:368-392`) は `¬hent_sum` を **by_cases で与えられていた**が、W-Y1 では h(W)=⊤ から
  **導く**必要があり enorm は no-op repackaging。Jensen は φ(r) を**上から**抑えるだけで裾積分の下界に使えない。

### 7-1. Approach — route α (EReal 単調性直接) を primary に

**鍵の再認識**: ゴールは A/B 分解でなく **EReal 単調性** `differentialEntropyExt (P.map W) ≤
differentialEntropyExt (P.map (W+V))`。これが直接出れば 3 枝が一括で閉じ、+∞ 伝播の A/B 分解 (T1/T2) は **全て不要**:
- ⊤ 枝: `h(W)=⊤ ≤ h(W+V) ⟹ h(W+V)=⊤` (`le_top` + antisymm)。B_{W+V}<⊤ の Jensen obstruction を回避。
- 有限枝: 単調性そのもの。⊥ 枝: `bot_le`。

⇒ **primary = route α** (EReal-conditioning)、**fallback = 明示 A/B** (route β + T1)。

### 7-2. route α (primary) — conditioning-reduces-entropy の EReal 化

機構: `h(W+V) ≥ h(W+V \| V) = h(W)`。in-tree Real 版が両方 genuine 既存:
- conditioning 減少 `condDifferentialEntropy_le` (`EPIG2ConvEntropyMonotone.lean:224`、`@audit:ok`、8 integrability)。
- fibre 同定 `condDifferentialEntropy_indep_add_eq` (`:328`、`@audit:ok`、c=1 で `h(W+V\|V)=h(W)`)。
- 差の KL 恒等式 `differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv`
  (`EPIG2ConvEntropyMonotone.lean` 系、`h(X)−h(X\|Z) = (klDiv joint product).toReal ≥ 0`)。

**障害 = 型壁**: これら全て `differentialEntropy : Measure ℝ → ℝ` (Bochner ℝ 値、h=±∞ 非表現) と
`.toReal` 経由で、有限性 precondition を本質的に持つ。EReal 化には:
- **(α-i) `condDifferentialEntropyExt : ... → EReal` 新規定義** + conditioning 不等式の EReal 版、または
- **(α-ii) KL 直接バイパス**: `I(W+V;V) = klDiv(joint ‖ product) ≥ 0` (Mathlib `InformationTheory.klDiv` は
  ℝ≥0∞ 値で非負 type-trivial) と chain rule `h(W+V) = h(W+V\|V) + I` を EReal で組む。⊤ 項を含む chain rule
  (`⊤ + nonneg = ⊤`、`⊤ − ⊤` 回避) の careful な EReal 算術が要る。

見積: **~150-300 行 + Real workhorse の EReal 化 blast radius** (傘 plan §設計制約「de Bruijn が normed field 要求で
Real 温存」と衝突しうる — workhorse は触らず上位に EReal 層を**足す**設計に限定する)。**multi-session、moonshot 規模**。
着手 1 手 = **(α-ii) KL バイパスの薄い prototype** を `lean-implementer` に試させ feasibility gate を取る
(EReal chain rule が ⊤ 項で破綻するか確認)。

### 7-3. route β (fallback) — 明示 A/B (route α が型壁で重すぎる場合)

- **T1 (B_{W+V}<⊤)**: 自作 **Jensen-下界** (φ=t·log t 下に有界 `≥−1/e`、affine minorant 経由)。
  部品 = `ConvexOn.exists_affine_le_real` (`Mathlib/Analysis/Convex/Approximation.lean:98`、verbatim:
  `(hsc : IsClosed s) (hfc : LowerSemicontinuousOn f s) (hf : ConvexOn ℝ s f) : ∃ c c', ∀ x∈s, c*x+c' ≤ f x`)。
  証明: a=∫f dμ で affine minorant `c·t+c' ≤ φ(t)` を取り積分 → `φ(a) = c·a+c' ≤ ∫φ(f)` (∫c(f−a)=0)。
  RHS well-defined (φ(f) ≥ integrable affine ⟹ 負部可積分)。capstone 補題1 の Jensen block を **W の負部
  B_W<⊤ から** bound する版に組み直す (`convDensityAdd_comm` `EPIConvDensity.lean:47` で対称)。~30-50 行、`hV_ac` 追加要。
- **T2 (A_{W+V}=⊤)**: route β でも循環は残る。truncation+LSC (route β') = W を有限エントロピー近似 W_n
  (conditioning truncation、route T `EPIInfiniteVarianceCapstone` 流用) → Real monotonicity → n→∞ を
  `klDiv_le_liminf_of_ae_tendsto` (`EPIG2KLFatouLSC.lean:112`) で LSC 持ち上げ。`wall:entropy-lsc-weak` 領域、
  W-Y2 と machinery 共有。⇒ route β は T2 が結局 LSC wall に当たるため、**route α の方が本筋**。

### 7-4. signature 設計確定 + 着手順

1. **`differentialEntropyExt_top_of_indep_add` に `hV_ac : (P.map V) ≪ volume` 追加** (案 F、honest
   regularity precondition)。消費先は未実装 `entropyPowerExt_add_ge_ac_unconditional` (両 a.c.) のみ → ripple 0。
   `rnDeriv_map_sum_ae` (両 a.c. 要) が呼べる。
2. **route α (α-ii KL バイパス) の feasibility gate** を最初に取る。通れば mono_add primitive 化、
   top_of_indep_add は系として削除可。
3. 通らなければ route β: T1 (自作 Jensen-下界、独立資産) を landing → B<⊤ 確保 → T2 を β' (LSC) に切替。
4. **判断点**: route α (型壁) も route β' (LSC wall) も 2-3 session 詰まれば、+∞ 伝播を `@residual(wall:…)` に
   昇格 (現 `plan:` から)、headline を `entropy_power_inequality_of_ac` (a.c.+有限エントロピー、proof-done) に確定
   (方針 X より strictly 強い honest 中間形)。これが L-Uncond-Y-roi 撤退口。

### 7-5. 撤退ライン (W-Y1 専用)

- **L-WY1-α** (route α 型壁): EReal chain rule が ⊤ 項 (`h(W)=⊤`) で `⊤−⊤=⊥` 等の退化に落ち、workhorse
  EReal 化が傘 plan の「Real 温存」設計制約と衝突 → route β (明示 A/B) に切替、T2 を LSC (W-Y2 と統合)。
- **L-WY1-β** (T1 Jensen-下界が組めない): `exists_affine_le_real` の LSC 前提が φ=t·log t (連続) で自明充足
  なので組める見込みだが、capstone 補題1 への配線が hell 化 → B<⊤ を route α 経由 (h(W+V)≥h(W) から自動) に一本化。
- **共通**: 詰まったら signature を結論形に保ち `sorry + @residual(plan:epi-uncond-deffix-monotone-plan)`。
  `*Hypothesis` bundle / 退化定義悪用 / 名前ロンダリング禁止。W-Y1 が genuine wall 化したら
  `@residual(wall:…)` に正しく昇格し独立 honesty-auditor を起動。

### 7-6. feasibility gate 結果 (2026-06-07、`lean-implementer` probe、scratch `/tmp/epi_route_alpha_probe.lean`)

route α-ii の machine probe verdict = **(B) multi-session moonshot だが path 可視、Mathlib-不能 wall ではない**。
crux が単一恒等式に局所化された。**§7 の本線を「恒等式 (i-a) 中心」に確定**:

- **crux 恒等式 (i-a)**: `differentialEntropyExt (P.map (W+V)) = differentialEntropyExt (P.map W)
  + ((klDiv ((P.map V) ⊗ₘ condDistrib (W+V) V P) ((P.map V) ⊗ₘ Kernel.const ℝ (P.map (W+V)))) : EReal)`
  (**`h(W) ≠ ⊥` 制限必須** — h(W)=⊥ では `⊥+⊤=⊥` ≠ 有限 LHS で FALSE、⊥ 枝は `bot_le` で別処理)。
  これ **1 本** が landing すれば gateway atom の +∞ 伝播・有限枝 sorry が**一括 closure**し、
  trichotomy 分解ごと不要化 (probe で `probe_mono_from_identity` が「恒等式 ⟹ mono 3 枝」を 0 sorry 確認)。
- **GREEN (probe で 0 sorry 通過、再利用可)**: (1) EReal 算術 `a ≤ a + (i:EReal)` (i:ℝ≥0∞、`add_le_add_right`、
  `a≠⊥` 制限**不要**)、(2) statement 化 + 恒等式⟹mono、(3) **coe 枝** (`_of_ac_integrable` で両辺
  `(differentialEntropy:EReal)` に落とし Real `differentialEntropy_add_ge_of_indep` を `exact_mod_cast` 持ち上げ
  → 8 integrability 供給できれば即閉、これは plan §3 所有の別 obligation で route α と独立)、(4) ⊤ 伝播の
  EReal 算術 (`⊤+klDiv=⊤`、`top_add_of_ne_bot`)。
- **RED (crux、self-build)**: 恒等式 (i-a) **本体**。h(W)=⊤ で Real bridge
  `differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv` (Bochner ℝ + `.toReal`、有限性必須) が
  使えない。2 道: **道 A (本筋)** = `condDifferentialEntropyExt : … → EReal` 新規定義 + 既存 genuine 2 lemma
  (`condDifferentialEntropy_indep_add_eq` fibre 同定 / chain rule) の EReal 版自作。**制約1 (constant fibre) で
  EReal Bochner 積分を組まず定数 fibre で済む** (independ 和の fibre は z 非依存定数 `h_ext(P.map W)`)。
  道 B (KL 直接 density) = 入口 `klDiv_eq_lintegral_klFun_of_ac` は Mathlib 存在だが condDistrib rnDeriv ↔ W+V
  density の繋ぎが Mathlib 不在 (loogle `ProbabilityTheory.condDistrib, MeasureTheory.Measure.rnDeriv` Found 0)
  → 道 A 優先。
- **着手順 (本線)**: ① EReal 版 fibre 同定 `condDifferentialEntropyExt_indep_add_eq` (定数 fibre、制約1 で軽い)
  → ② EReal chain rule `h_ext(X) = condDifferentialEntropyExt(X|Z) + (klDiv:EReal)` (Real bridge steps a/b/c の
  lintegral 持ち上げ = crux 本体) → ③ ①② 合成で (i-a) → ④ gateway atom を「(i-a)+算術」の薄い 2-lemma に
  rewrite (trichotomy 廃止)。
- **classification 据置**: `plan:epi-uncond-deffix-monotone-plan` (known-shape self-build、Mathlib 壁でない)。
  道 A chain rule (②) が型壁で 2-3 session 詰まれば §7-4 判断点で `wall:` 昇格。

# 無条件 EPI — entropyPowerExt def-fix + 拡張単調性 campaign

> **親**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) (傘 moonshot)。本 plan は傘の **Phase 1 (S1 retype) の defect 訂正 + Phase 5 dispatch 再構成** を担う。
> **slug**: `epi-uncond-deffix-monotone-plan`。
> **status**: 2026-06-06 起草。`entropyPowerExt` の **false-statement defect を機械検証で発見** → 訂正 def を validated prototype 化 (`/tmp/epi_deffix_proto.lean` compiles) → 実装 campaign。

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
- **+∞ 枝** (diffEntExt W = ⊤): diffEntExt(W+V)=⊤ 要 (+∞ 伝播)。**Mathlib 壁でなく拡張 entropy plumbing**。今 session で閉じれば genuine、無理なら `sorry + @residual(plan:epi-uncond-deffix-monotone-plan)` (plan slug、wall でない)。

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
- [~] **P2 拡張単調性** `entropyPowerExt_mono_add` — **本 session では未着手 (deferred)**。infinite-entropy (±∞) 入力の `entropyPowerExt` 単調性。dispatch を **finite-entropy precondition で scope** することで回避 (下記 P3)。+∞ 伝播 (`h(W)=+∞, V indep ⟹ h(W+V)=+∞`) は extended-entropy plumbing (Mathlib 壁でなく)、後続で着手 → `plan:epi-uncond-deffix-monotone-plan`。
- [x] **P3 dispatch 再構成** ✅ (`EPIUncondMixedCase.lean`、2026-06-06): case-2 `entropyPowerExt_mixed_add_ge` (+ symm) に finite-entropy 前提 `hX_ent`/`hW_ent` 追加 + `_of_ac_integrable` 使用 (genuine 維持)。case-1 の **false-as-stated だった bare sorry を named wall `entropyPowerExt_add_ge_finite_ac` (`@residual(wall:epi-finite-entropy-ac-classical)`) に置換**。dispatch は finite-entropy 4 前提を thread (方針 X partial scope)。**case-2/3/symm sorryAx-free 維持、唯一の sorry = named wall 1 本**。
- [x] **P4 独立 honesty-auditor** ✅ (2026-06-06): 13 declaration 監査 = 11 ok / 1 honest_residual (named wall) / 1 dispatch transitive sorry / **0 defect**。訂正 def の退化非悪用 (±∞ 正写像) 機械検証、finite-entropy 前提の non-load-bearing 確認、`wall:epi-finite-entropy-ac-classical` 分類妥当性 (一般 a.c. 無限分散 = Lieb-Young 不在 loogle Found 0) を独立確認。`@audit:ok` 付与済。
- [x] **P5 wall register 登録 + commit** ✅: `audit-tags.md` Wall name register に `epi-finite-entropy-ac-classical` 追記。

### 到達点 (本 session、2026-06-06)
**無条件 headline `entropyPowerExt_add_ge_dispatch_skeleton` は def-fix で TRUE-as-stated 化、唯一の sorry = `wall:epi-finite-entropy-ac-classical` (両 a.c. 有限エントロピー古典 EPI) 1 本に局所化。** 旧状態「false-as-stated monolithic sorry」→「sound + 精密 named wall 1 本」へ昇格。残: (a) named wall closure (正則=Phase A 済、有限分散=方針 X、無限分散=genuine 壁)、(b) infinite-entropy 入力の precondition 撤去 (+∞ 伝播 = P2)。

## 5. 撤退ライン

- **P1 def-fix が downstream を大量破壊**: case-2 を mono 化する前に EntropyPowerExt 単体を clean にし、`_of_ac` 利用箇所 (sanity gate / case-2) を順に修復。詰まれば `entropyPowerExt_of_ac_integrable` に finite-entropy precondition を honest に追加 (load-bearing でない)。
- **P2 +∞ 伝播が今 session 不可**: `sorry + @residual(plan:epi-uncond-deffix-monotone-plan)` で park (wall でなく plan、後続 closeable)。case-1b 無限 entropy 枝も同 residual 経由 (mono に乗る)。
- **共通**: 詰まったら signature を結論形に保ち `sorry + @residual`。`*Hypothesis` bundle / 退化定義悪用 / 名前ロンダリング禁止。`_unconditional` 命名は threaded integrability precondition が残る間は name-laundering ゆえ不可 (傘 Phase 5 判断ログ 2 と整合)。

## 6. honest 到達点 (本 session target)

headline TRUE-as-stated (def-fix)。genuine close: singular/mixed/(−∞ or 0 entropy)/(+∞ entropy if 伝播閉)。残 named wall: (a) +∞ 伝播 (閉じなければ、plan slug)、(b) `wall:epi-finite-entropy-ac-classical` (両有限 entropy 一般 a.c. の古典 EPI、方針 X partial + 無限分散 wall)。**現状の「false-as-stated monolithic sorry」から「true-as-stated + 精密 named wall 1-2 本」への昇格が成果**。

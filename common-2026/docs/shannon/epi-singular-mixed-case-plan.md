# EPI 無条件化 — 特異・混合 case (S3) サブ計画 🌙

> **Parent**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) §柱 2 (3-case 分岐) + §Phase 4。
> **slug**: `epi-singular-mixed-case-plan` (`@residual(plan:epi-singular-mixed-case-plan)` と一致)。
> **scope**: 3-case 分岐のうち **case 2 (X a.c. ∧ Y 特異)** + **case 3 (両特異)** の補題群を、
> S1 完成済の `entropyPowerExt : Measure ℝ → ℝ≥0∞` 上で **genuine 化** する。3-case 判定 dispatch の
> スケルトン (case 2/3 補題 + 判定構造) までを担当。最終 3-case assembly (headline 型) は S2 statement 層を
> 要するため傘 plan **Phase 5 に defer**。

<!--
記法: 状態絵文字 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更(判断ログ参照)。
取り消し線 = 廃止 Phase。判断ログ append-only。
rg "^- \[ \]" で残タスク横断、rg "🔄" でピボット拾い。
-->

## 前提 — S1 genuine 完成済 (利用可能な部品、verbatim 確認済 2026-06-05)

新 file `InformationTheory/Shannon/EntropyPowerExt.lean` が **genuine 0 sorry** で着地済 (commit `3421948`)。
本 plan が呼び出す部品 (`EntropyPowerExt.lean`、verbatim 確認済):

| 部品 (file:line) | signature 要点 | 本 plan での用途 |
|---|---|---|
| `entropyPowerExt` (`:40`) | `(μ : Measure ℝ) : ℝ≥0∞ := EReal.exp (2 * differentialEntropyExt μ)` (非分岐) | case 2/3 結論型 |
| `entropyPowerExt_singular` (`:64`) | `(h : ¬ μ ≪ volume) → entropyPowerExt μ = 0` | case 3 で `N(X)=N(Y)=0`、case 2 で `N(Y)=0` |
| `entropyPowerExt_of_ac` (`:56`) | `(h : μ ≪ volume) → entropyPowerExt μ = ENNReal.ofReal (Real.exp (2 * differentialEntropy μ))` | case 2 で Real→ℝ≥0∞ lift |
| `entropyPowerExt_dirac` (`:71`) | `entropyPowerExt (Measure.dirac m) = 0` | sanity (特異 → 0) |
| `entropyPowerExt_gaussianReal` (`:81`) | `(hv : v ≠ 0) → entropyPowerExt (gaussianReal m v) = ENNReal.ofReal (2πe·v)` | sanity (a.c. → 非退化) |

case 2 の Real 中核資産 (`EPIG2ConvEntropyMonotone.lean`、両 genuine `@audit:ok`、verbatim 確認済):

| 補題 (file:line) | conclusion (verbatim) | 前提の要点 |
|---|---|---|
| `condDifferentialEntropy_le` (`:224`) | `condDifferentialEntropy X Z μ ≤ differentialEntropy (μ.map X)` | `hX hZ Measurable`、`hX_ac : μ.map X ≪ volume`、+ **8 integrability precondition** (下記 box) |
| `condDifferentialEntropy_indep_add_eq` (`:328`) | `condDifferentialEntropy (fun ω => X ω + c * Z ω) Z μ = differentialEntropy (μ.map X)` | `hX hZ Measurable`、`hXZ : IndepFun X Z μ`、`hX_ac : μ.map X ≪ volume` |
| `differentialEntropy_indep_gaussian_add_ge` (`:378`) | `h(μ.map X) ≤ h(μ.map (X + √s·Z))` | 上 2 補題を Gaussian Z で合成済 **= 一般 Y 版の threading 雛形** |

---

## 進捗

- [ ] Phase 0 — feasibility 検算 (case 2 integrability 前提が混合設定で充足可能か、最終 verbatim 照合) 📋
- [ ] Phase 1 — case 3 (両特異) 補題 (`zero_le` 自明、最 soft) 📋
- [ ] Phase 2 — convolution-a.c. 補題 (`X a.c. ∧ X⊥Y ⟹ X+Y a.c.`、3 行) 📋
- [ ] Phase 3 — case 2 Real 中核 `h(X) ≤ h(X+Y)` (2 補題 `c=1` 合成 + integrability threading) 📋
- [ ] Phase 4 — case 2 ℝ≥0∞ lift `N(X+Y) ≥ N(X)` + X↔Y 対称版 📋
- [ ] Phase 5 — 3-case 判定 dispatch スケルトン (case 2/3 配線、case 1 / headline は S2/傘 Phase 5 待ち) 📋

proof-log: Phase 0 のみ `no` (検算のみ)。Phase 1–5 は `yes`
(`docs/shannon/proof-log-epi-singular-mixed-case.md` に追記、各 Phase 着地時)。

**着地 file**: `InformationTheory/Shannon/EPIUncondMixedCase.lean` (新規、`EntropyPowerExt` +
`EPIG2ConvEntropyMonotone` を import)。S1 が `entropyPowerExt` を提供済なので、本 plan は
**Real 中核と ℝ≥0∞ lift の両方を同 file で着地できる** (在庫 skeleton の「S1 未着地ゆえ Real 先行」
注記は S1 完成で解消、ℝ≥0∞ lift も本 plan scope 内)。

---

## ゴール / Approach

傘 plan §柱 2 の 3-case のうち case 2 + case 3 を `entropyPowerExt` 上で genuine 化する。
**最終 3-case dispatch assembly (headline 主定理) は S2 statement 層を要するため傘 Phase 5 に defer**。
本 plan が締めるのは「case 2/3 の補題 + 3-case 判定構造のスケルトン」まで。

### Approach (解の全体形)

3-case を `(P.map X ≪ volume)` × `(P.map Y ≪ volume)` の `by_cases` で分岐する。新 ℝ≥0∞
`entropyPowerExt` は特異枝で `0` (退化トラップ除去済)、a.c. 枝で `ofReal (exp (2h))`。

#### case 3 (両特異) — 最 soft、~20-40 行

X, Y とも特異。`entropyPowerExt_singular` で `N(X) = N(Y) = 0` → RHS = `0 + 0 = 0`。
LHS `entropyPowerExt (P.map (X+Y)) ≥ 0` は **ℝ≥0∞ で型自明** (`zero_le`)。X+Y が a.c. か特異かを
**判定せずに** 閉じる (RHS=0 なので LHS の値に依らず不等式成立)。退化定義悪用ではない:
特異測度のエントロピーパワーは真に 0 であり、RHS=0 は正しい値。L-Uncond-0-γ クリア。

#### case 2 (X a.c. ∧ Y 特異) — conditioning-reduces-entropy 2 補題合成

`entropyPowerExt_singular` で `N(Y) = 0` → RHS = `N(X) + 0 = N(X)`。よって `N(X+Y) ≥ N(X)` を示せば足りる。
これを 3 段で組む:

1. **X+Y a.c. 判定** (Phase 2、3 行 0 sorry): `X a.c. ∧ X⊥Y ⟹ X+Y a.c.`。
   `IndepFun.map_add_eq_map_conv_map` (`μ.map(X+Y) = μ.map X ∗ μ.map Y`) → `Measure.conv_comm`
   (a.c. 因子 `μ.map X` を右に回す、`conv_absolutelyContinuous` は a.c. 因子を右に要求する非対称形) →
   `Measure.conv_absolutelyContinuous` (a.c. 伝播)。両 Mathlib lemma 存在確認済
   (loogle 2026-06-05: `MeasureTheory.Measure.conv_absolutelyContinuous` /
   `ProbabilityTheory.IndepFun.map_add_eq_map_conv_map`)。これで RHS=N(X) の lift と
   case 2 の a.c. 枝判定 (`entropyPowerExt_of_ac` を X+Y に適用) の両方に必要な
   `μ.map(X+Y) ≪ volume` が出る。

2. **Real 中核 `h(X) ≤ h(X+Y)`** (Phase 3): `condDifferentialEntropy_indep_add_eq` (`c=1`, `Z:=Y`)
   で `h(X+Y | Y) = h(X)`、`condDifferentialEntropy_le` (`X:=X+Y`, `Z:=Y`) で `h(X+Y | Y) ≤ h(X+Y)`。
   合成して `h(X) = h(X+Y|Y) ≤ h(X+Y)`。`differentialEntropy_indep_gaussian_add_ge` (`:378`) が
   Gaussian Z で同じ合成を threading 済 = **一般 Y 版の雛形** (Gaussian 固有の `hZ_law` を外すだけ)。

3. **ℝ≥0∞ lift `N(X+Y) ≥ N(X)`** (Phase 4): X, X+Y 共に a.c. なので
   `entropyPowerExt_of_ac` で両者 `ofReal (exp (2h))`。`Real.exp_le_exp.mpr` (h(X)≤h(X+Y) を
   `2h(X)≤2h(X+Y)` 経由) → `ENNReal.ofReal_le_ofReal` で lift。RHS は `N(X)+N(Y) = N(X)+0 = N(X)`
   を `entropyPowerExt_singular hY_sing` + `add_zero` で。

**X↔Y 対称版** (Y a.c. ∧ X 特異): `X+Y = Y+X` を `add_comm` で噛ませて同補題を再利用するか、
引数の X/Y を入れ替えて再適用。`IndepFun` は対称 (`hXY.symm`)。

#### 3-case 判定 dispatch (Phase 5、スケルトンのみ)

`P.map X ≪ volume` / `P.map Y ≪ volume` を `by_cases` で 4 通りに分岐:
両 a.c. (case 1)、X のみ a.c. (case 2)、Y のみ a.c. (case 2 対称)、両特異 (case 3)。
case 2/3 枝を本 plan の補題で配線。**case 1 枝は既存 plan 群 (`epi-stam-to-conclusion-plan` 等)
の closure 待ち、headline 主定理 statement は S2 の型を要する** → 本 plan は case 2/3 枝の
配線可能性を示すスケルトン (`by_cases` 構造 + case 2/3 補題呼出) まで。最終 dispatch theorem
(`entropy_power_inequality_unconditional`) の body 完成は傘 Phase 5。

### S1/S2 依存の線引き (重要)

傘 plan dep DAG は `S1 → S2 → {S3, case1}`。だが **case 2/3 の補題自体は `entropyPowerExt`
(S1 完成済) に直接立つ** — S2 (downstream re-port) を待たない。S2 待ちなのは
**最終 3-case dispatch assembly (headline 主定理)** のみ (主定理 statement が S2 で確定する
新型 `entropyPowerExt` consumer 配線に依存)。Phase 表で線引き:

| Phase | 依存 | 起動可能タイミング |
|---|---|---|
| Phase 0 (検算) | — | 即 (verbatim 照合のみ) |
| Phase 1 (case 3) | S1 (`entropyPowerExt_singular`) | **S1 完成済 → 即** |
| Phase 2 (conv-a.c.) | Mathlib のみ | **即** (S1 不要、純 Mathlib) |
| Phase 3 (Real 中核) | `EPIG2ConvEntropyMonotone` 既存 | **即** (S1 不要、Real 層) |
| Phase 4 (ℝ≥0∞ lift) | S1 + Phase 3 | **S1 完成済 → 即** |
| Phase 5 (dispatch スケルトン) | Phase 1+4 | Phase 1–4 後 |
| (headline assembly) | **S2 + S5 + case1** | **傘 Phase 5、本 plan scope 外** |

⇒ 本 plan の Phase 1–5 は **全て S2 を待たずに着地可能**。S2 待ちは headline のみで、それは defer。

---

## Phase 0 — feasibility 検算 (case 2 integrability 前提充足性) 📋

proof-log: no (検算のみ、実装着手しない)。

傘 Phase 0-B の case 2 宿題 = 「`condDifferentialEntropy_le` の integrability 前提が
『X a.c.、Y 特異』設定で充足可能か」の最終 verbatim 照合。**在庫
`epi-uncond-mixed-case-inventory.md` で実機 typecheck 済 + 本起草で再 verbatim 確認済**:

- [ ] `condDifferentialEntropy_le` (`:224-245`) の全前提を `X:=X+Y` (a.c.)、`Z:=Y` (特異) で照合。
  Y に課す前提は **`hZ : Measurable Y` のみ** (`:226`)。残り全前提 (`hX_ac`, `h_ac`, `h_int`,
  `hκ_v`, `hκ_logp_int`, `hκ_cross_int`, `h_fibreEnt_int`, `h_cross_int`, `h_logq_int`) は
  **W=X+Y の a.c. 密度 + fibre 上の regularity** に関するもの。Y の特異性は阻害しない。
- [ ] `[StandardBorelSpace]` 不要を確認 (verbatim: `condDifferentialEntropy_le` は
  `[MeasurableSpace Ω] [MeasurableSpace α]` のみ、`:225`)。
- [ ] **X も特異な混合は case 2 でなく case 3** (RHS の a.c. 項消失) を確認 → case 2 は
  「X a.c. ∧ Y 特異」に限定して良い。X 特異側は Phase 5 dispatch の by_cases が case 3 へ流す。

### Phase 0 検算 verdict (2026-06-05 起草時、verbatim 確認済)

**GO**: case 2 integrability 前提は全て W=X+Y (a.c.) の regularity precondition であり、Y が特異でも
`hZ : Measurable Y` 以外何も Y に要求しない。`differentialEntropy_indep_gaussian_add_ge` (`:378`) が
Gaussian Z で同型 8 前提を genuine threading 済 = 一般 Y 版も同形で threading 可能。
**L-Uncond-0-β / L-Uncond-4-α は不発見込み** (前提充足性に起因する縮退は起きない)。

### Phase 0 撤退ライン

- **L-Uncond-0-β** (傘から継承、case 2 NO-GO): `condDifferentialEntropy_le` の integrability 前提が
  混合設定で充足不能 (= 上記 verdict が実装で覆る) → case 2 を honest precondition 付き partial に留め、
  無条件性を「両 a.c. ∨ 両特異」に縮小。**現 verdict は不発**だが、threading 実装で予想外の
  Y 特異依存が出たら発動。

---

## Phase 1 — case 3 (両特異) 補題 📋

proof-log: yes。最 soft (~20-40 行)。

- [ ] `entropyPowerExt_singular_add_ge` (両特異): `(hX_sing : ¬ P.map X ≪ volume)
  (hY_sing : ¬ P.map Y ≪ volume) → entropyPowerExt (P.map (X+Y)) ≥
  entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)`。
  証明: `entropyPowerExt_singular hX_sing` + `entropyPowerExt_singular hY_sing` で RHS `= 0 + 0`、
  `add_zero` + `zero_le` で `LHS ≥ 0`。X+Y の a.c./特異 判定 **不要** (RHS=0)。

### Phase 1 撤退ライン

- なし (型自明)。詰まれば `sorry` + `@residual(plan:epi-singular-mixed-case-plan)`、但し ℝ≥0∞ の
  `zero_le` で閉じる見込みで撤退口は不発。退化定義悪用ではない (特異測度のエントロピーパワーは真に 0)。

### Phase 1 verify

- [ ] `lake env lean InformationTheory/Shannon/EPIUncondMixedCase.lean` 0 errors (Phase 1 補題のみ着地時)。

---

## Phase 2 — convolution-a.c. 補題 📋

proof-log: yes。在庫で実機 typecheck 済の 3 行、純 Mathlib (S1 不要)。

- [ ] `map_add_absolutelyContinuous`: `(hX : Measurable X) (hY : Measurable Y)
  (hXY : IndepFun X Y P) (hX_ac : P.map X ≪ volume) → P.map (fun ω => X ω + Y ω) ≪ volume`。
  証明 (在庫 verbatim、実機閉):
  ```
  rw [show (fun ω => X ω + Y ω) = X + Y from rfl,
    hXY.map_add_eq_map_conv_map hX hY, Measure.conv_comm]
  exact Measure.conv_absolutelyContinuous hX_ac
  ```
  注意: `conv_absolutelyContinuous` は a.c. 因子を**右**に要求する非対称形 → `conv_comm` を 1 段噛ます。

### Phase 2 撤退ライン

- **L-Uncond-4-β** (傘から継承、X+Y の a.c. 判定 lemma 不在) → **不発確定** (loogle 2026-06-05 で
  `conv_absolutelyContinuous` / `map_add_eq_map_conv_map` 両存在確認)。万一 instance 解決
  (`ρ.IsAddLeftInvariant` / `SFinite`) が ℝ で自動発火しなければ明示供給 (在庫は自動解決と記載)。

### Phase 2 verify

- [ ] `lake env lean ...` 0 errors。

---

## Phase 3 — case 2 Real 中核 `h(X) ≤ h(X+Y)` 📋

proof-log: yes。2 補題 `c=1` 合成 + 8 integrability precondition の honest threading。

- [ ] `differentialEntropy_add_ge_of_indep`: `(hX hY : Measurable) (hXY : IndepFun X Y P)
  (hX_ac : P.map X ≪ volume) → [bridge integrability 群 8 本 を W=X+Y, Z=Y で honest precondition]
  → differentialEntropy (P.map X) ≤ differentialEntropy (P.map (fun ω => X ω + Y ω))`。
  証明 (`differentialEntropy_indep_gaussian_add_ge` `:378` を雛形に、Gaussian 固有部を外す):
  - `h_fibre := condDifferentialEntropy_indep_add_eq X Y P 1 hX hY hXY hX_ac` で
    `h(X+1·Y | Y) = h(X)` (`c=1`)。
  - `h_le := condDifferentialEntropy_le (X+Y) Y P hW hY hW_ac h_ac h_int hκ_v hκ_logp_int
    hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int` で `h(X+Y|Y) ≤ h(X+Y)`。
    `hW_ac` は Phase 2 の `map_add_absolutelyContinuous` から供給。
  - `rw [← h_fibre]; exact h_le`。
- [ ] **8 integrability precondition の signature 配置**: `condDifferentialEntropy_le` の
  `h_ac / h_int / hκ_v / hκ_logp_int / hκ_cross_int / h_fibreEnt_int / h_cross_int / h_logq_int`
  (`:228-245` verbatim) を `X:=X+Y`, `Z:=Y` で本補題の **honest precondition** として載せる。
  **`*Hypothesis` predicate に bundle するのは禁止** (CLAUDE.md load-bearing 兆候)。これらは
  regularity precondition (W=X+Y の a.c. 密度 + fibre regularity)。`differentialEntropy_indep_gaussian_add_ge`
  の signature (`:382-405`) が **そのまま雛形** (`Real.sqrt s * Z` を `Y` に置換、`s` 引数を消す)。

### Phase 3 撤退ライン

- **L-Uncond-4-α** (case 2 前提不足): integrability threading が雛形から乖離し signature 肥大 →
  当該 precondition を `sorry` + `@residual(plan:epi-singular-mixed-case-plan)` で park。
  **仮説束化禁止** (bundle した predicate で `sorry` を消すのは tier 5 defect)。Gaussian 版が
  genuine threading 済なので一般 Y 版も閉じる見込み高、park は最小限。

### Phase 3 verify

- [ ] `lake env lean ...` 0 errors。precondition が全て regularity であることを docstring に明記
  (「NOT load-bearing、W=X+Y の a.c. 密度 + fibre regularity」)。

---

## Phase 4 — case 2 ℝ≥0∞ lift + X↔Y 対称版 📋

proof-log: yes。S1 `entropyPowerExt_of_ac` / `_singular` を被せる薄いラッパ。

- [ ] `entropyPowerExt_mixed_add_ge` (X a.c. ∧ Y 特異): `(hX hY : Measurable) (hXY : IndepFun X Y P)
  (hX_ac : P.map X ≪ volume) (hY_sing : ¬ P.map Y ≪ volume) → [Phase 3 の integrability 群]
  → entropyPowerExt (P.map (X+Y)) ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)`。
  証明:
  - RHS: `entropyPowerExt_singular hY_sing` で `N(Y) = 0`、`add_zero` で RHS `= N(X)`。
  - `hW_ac := map_add_absolutelyContinuous X Y P hX hY hXY hX_ac` (Phase 2)。
  - `entropyPowerExt_of_ac hX_ac` で `N(X) = ofReal (exp (2 h(X)))`、
    `entropyPowerExt_of_ac hW_ac` で `N(X+Y) = ofReal (exp (2 h(X+Y)))`。
  - `differentialEntropy_add_ge_of_indep` (Phase 3) で `h(X) ≤ h(X+Y)` →
    `2 h(X) ≤ 2 h(X+Y)` → `Real.exp_le_exp.mpr` → `ENNReal.ofReal_le_ofReal` で `N(X) ≤ N(X+Y)`。
- [ ] `entropyPowerExt_mixed_add_ge_symm` (Y a.c. ∧ X 特異): `add_comm` で `X+Y = Y+X` を噛ませ
  `entropyPowerExt_mixed_add_ge` に Y/X を入替えて再適用 (`hXY.symm` で `IndepFun Y X P`)。
  `differentialEntropy_map_add_comm` 系 / `P.map (X+Y) = P.map (Y+X)` の同一視が要るか Phase 4 で確認
  (要 in-tree 補題 or `add_comm` の funext)。

### Phase 4 撤退ライン

- **L-Uncond-4-β** (継承): X+Y の a.c. 判定は Phase 2 で閉じ済 → 不発。
- 対称版で `P.map (X+Y) = P.map (Y+X)` の同一視補題が in-tree 不在なら `funext` + `add_comm` で
  measure 同値を示す (純 Mathlib、壁でない)。

### Phase 4 verify

- [ ] `lake env lean ...` 0 errors。**非自明値 sanity**: case 2 で `N(X) > 0` (X a.c.、`exp > 0`)、
  `N(Y) = 0` (Y 特異) を `entropyPowerExt_gaussianReal` / `entropyPowerExt_dirac` で例示確認
  (退化定義悪用でないことの L-Uncond-0-γ gate)。

---

## Phase 5 — 3-case 判定 dispatch スケルトン 📋

proof-log: yes。case 2/3 配線のスケルトン。**headline 主定理 body 完成は傘 Phase 5 (S2 待ち)**。

- [ ] `entropyPowerExt_add_ge_dispatch_skeleton`: `(hX hY : Measurable) (hXY : IndepFun X Y P)
  → entropyPowerExt (P.map (X+Y)) ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)` を
  `by_cases hX_ac : P.map X ≪ volume` / `by_cases hY_ac : P.map Y ≪ volume` の 4 分岐で組む:
  - 両特異 (`¬hX_ac ∧ ¬hY_ac`): Phase 1 `entropyPowerExt_singular_add_ge`。
  - X a.c. ∧ Y 特異: Phase 4 `entropyPowerExt_mixed_add_ge` (+ Phase 3 integrability を供給)。
  - Y a.c. ∧ X 特異: Phase 4 `entropyPowerExt_mixed_add_ge_symm`。
  - **両 a.c. (case 1)**: `sorry` + `@residual(plan:epi-stam-to-conclusion-plan)` で park
    (既存 plan 群が closure する hard core、本 plan scope 外)。または傘 Phase 5 で
    case1 補題を渡す形に signature 化。
- [ ] **線引き明示**: 本 plan のスケルトンは「case 2/3 枝が genuine、case 1 枝は既存 plan park、
  integrability precondition は honest threading」。最終 headline
  `entropy_power_inequality_unconditional` (S2 で確定する新型 statement、case1 を S5 経由無前提版に
  差替) の body 完成は **傘 Phase 5**。本 plan は case 2/3 補題が dispatch に配線可能なことを示すまで。
- [ ] **独立 honesty-auditor 起動** (case 1 park 以外に新規 `sorry`/`@residual` を導入した場合、
  CLAUDE.md 必須): dispatch の honesty (case 3 が vacuous でないか、case 2 の前提が load-bearing でなく
  regularity か) を独立検証。

### Phase 5 撤退ライン

- **L-Uncond-5-β** (傘から継承): dispatch が case 1 の残 sorry を transitive 消費 → 部分達成として
  honest 命名で commit。docstring に「case 2/3 + dispatch 構造は genuine、case 1 (両 a.c.) は
  `epi-stam-to-conclusion-plan` closure 待ち」明示。compound `@residual` で case1 plan を指す。
- **L-Uncond-5-α** (`by_cases (P.map X ≪ volume)` の `Decidable`): classical で組むと axioms に
  `Classical.choice` が増えるが sorryAx ではない (propext/Quot.sound と同列、honest)。問題なし。

### Phase 5 verify

- [ ] `lake env lean ...` 0 errors。`#print axioms entropyPowerExt_add_ge_dispatch_skeleton` で
  case 2/3 枝の sorryAx 依存を実測 (case 1 park 分の sorryAx は honest、その旨 docstring)。
- [ ] 完了時 `InformationTheory.lean` に `import InformationTheory.Shannon.EPIUncondMixedCase` 追加。

---

## 撤退ライン共通規律

全 Phase 共通禁止 (CLAUDE.md 検証の誠実性): `Prop := True` placeholder / 結論型≡仮説型 `:= h` 循環 /
load-bearing `*Hypothesis` predicate に integrability 群を bundle / **退化定義悪用** (case 3 の RHS=0 を
突いた vacuous 達成に見えうるが、特異測度のエントロピーパワーは真に 0 なので OK。LHS が常時 0 になる
定義ミスは Phase 4 の `entropyPowerExt_gaussianReal` sanity で検出)。

**honest 撤退口**: 詰まったら `sorry` + `@residual(plan:epi-singular-mixed-case-plan)` (case 1 park は
`@residual(plan:epi-stam-to-conclusion-plan)`)。integrability precondition を park する場合も signature は
honest precondition のまま保ち、bundle 化しない。新規 `sorry` + `@residual` 導入時は独立 honesty-auditor 起動。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-06-05 起草**: 傘 plan §柱 2 + §Phase 4 + 在庫 `epi-uncond-mixed-case-inventory.md` を受けて
   case 2/3 のサブ計画を起草。S1 (`EntropyPowerExt.lean`、commit `3421948`) genuine 完成済の部品
   (`entropyPowerExt_singular` / `_of_ac` / `_dirac` / `_gaussianReal`) を verbatim 確認し、本 plan が
   Real 中核 + ℝ≥0∞ lift の両方を同 file (`EPIUncondMixedCase.lean`) で着地する構造に確定
   (在庫 skeleton の「S1 未着地ゆえ Real 先行」は S1 完成で解消)。
   - **case 2 integrability feasibility verdict = GO** (Phase 0 検算): `condDifferentialEntropy_le`
     (`:224-245`) の全前提を verbatim 照合した結果、Y に課すのは `hZ : Measurable Y` のみ
     (`:226`)、残り 8 integrability precondition は全て W=X+Y (a.c.) の密度 + fibre regularity。
     Y の特異性は阻害しない。`differentialEntropy_indep_gaussian_add_ge` (`:378`) が Gaussian Z で
     同型 8 前提を genuine threading 済 = 一般 Y 版の雛形。⇒ **L-Uncond-0-β / L-Uncond-4-α 不発見込み**。
   - **L-Uncond-4-β (X+Y a.c. 判定) 不発確定**: loogle 2026-06-05 で
     `MeasureTheory.Measure.conv_absolutelyContinuous` + `ProbabilityTheory.IndepFun.map_add_eq_map_conv_map`
     両存在確認 (3 行 0 sorry、`conv_comm` を 1 段噛む非対称形)。
   - **S1/S2 依存の線引き**: case 2/3 補題は `entropyPowerExt` (S1 完成済) に直接立つため Phase 1–5 は
     **全て S2 を待たず着地可能**。S2 待ちは headline 主定理 assembly のみ → 傘 Phase 5 に defer。
     本 plan scope は case 2/3 補題 + dispatch スケルトンまで、headline body は含まない。

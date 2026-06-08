# EPI 無条件化 Phase 5 — 無条件 dispatch endgame サブ計画 🌙

> **Parent**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) §Phase 5 (S4 = assembly)
> **slug**: `epi-uncond-dispatch-endgame-plan` (= parent Phase 5 / S4 が参照する slug、`@residual(plan:epi-uncond-dispatch-endgame-plan)` と一致)。
> **status**: 📋 起草 (2026-06-08)。method-Y full gateway (S5) proof-done を受けた **headline wire endgame**。既存 21-precondition dispatch を gateway で全除去し、`hX hY hXY` のみの完全無条件 dispatch を**別建て**で構築する。

<!--
記法は moonshot-plan-template と同じ (状態絵文字 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更、判断ログ append-only)。
予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。proof-done / sorryAx-free 等の機械再導出可能 fact は
prose にキャッシュせず `#print axioms` で都度確認 (CLAUDE.md「re-derive > cache」)。
-->

## 進捗

- [ ] Phase 0 — 在庫 gate (EReal exp 境界値 + RHS 確定補助の在庫指示) 📋
- [ ] Phase 1 — 柱 A: singular-case rewire (case 2 / case 2 対称) skeleton + proof 📋
- [ ] Phase 2 — 柱 B: case-1 split (⊤/⊥/有限 sub-case) skeleton + proof 📋
- [ ] Phase 3 — 柱 C: 完全無条件 dispatch assembly + #print axioms 検証 📋
- [ ] Phase 4 — 柱 D: headline 命名 + 親 Phase 5 同期 📋

proof-log: Phase 0 = no (調査のみ)。Phase 1–4 = yes (`docs/shannon/proof-log-epi-uncond-dispatch-endgame-*.md`)。

## ゴール / Approach

### ゴール

既存の無条件 gateway 群 (S5 = method-Y、全て proof-done) を使い、現 dispatch
`entropyPowerExt_add_ge_dispatch_skeleton` (`EPIUncondDispatch.lean:145`、proof-done だが **21
precondition** = case2/2symm 用 16 integrability + case-1/case2 用 5 finite-entropy) の precondition を
**全除去**し、`(hX hY : Measurable) (hXY : IndepFun X Y P)` **のみ**を取る完全無条件 dispatch を
**新 file `EPIUncondDispatchFull.lean` に別建て**で構築する。最終定理 (拡張版):

```
entropyPowerExt (P.map (X+Y)) ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)
```

を `hX hY hXY` のみで `#print axioms` sorryAx-free に達成する。既存 21-precondition skeleton は
proof-done ゆえ**改変せず残す** (consumer 0 の leaf、機械確認済)。

### Approach (解の全体形 — 4 つの柱)

無条件 gateway `entropyPowerExt_mono_add_unconditional` (= `N(W+V) ≥ N(W)`、integrability/有限性
仮説ゼロ、regularity のみ、`@audit:ok`) を core engine とする。RHS = `N(X)+N(Y)` の各項を
gateway 単調性で `N(X+Y)` の下界に潰すか、有限 sub-case で既存 case-1 genuine EPI に落とす。

- **柱 A (singular case rewire)**: case 2 (X a.c. ∧ Y 特異) は `N(Y)=0` ゆえ RHS=`N(X)`。
  gateway `mono_add_unconditional X Y` で `N(X+Y) ≥ N(X)` で closure。**integrability 8 本 +
  finite-entropy 2 本除去**。対称版も同型 (gateway W=Y,V=X + `IndepFun.symm` + `add_comm`)。
- **柱 B (case-1 split = endgame 本体)**: case 1 (両 a.c.) を `h(X+Y)` / `h(X)` / `h(Y)` の
  ⊤/⊥/有限で by_cases split し、各 sub-case を gateway 単調性 (⊤/⊥ 枝で RHS の一項が ⊤/0 に潰れる)
  または有限 sub-case で bridge `differentialEntropyExt_integrable_of_finite` → 既存 genuine
  `entropyPowerExt_add_ge_finite_ac` (3 finite-entropy precondition) に落とす。
- **柱 C (assembly)**: 4 枝 by_cases (X a.c. × Y a.c.) → 柱B (case1) / 柱A (case2) / 柱A対称
  (case2symm) / `entropyPowerExt_singular_add_ge` (case3) を組む。signature は `hX hY hXY` のみ。
- **柱 D (命名)**: 拡張版 headline `entropy_power_inequality_extended_unconditional` (仮名)。
  ⚠ 真の無条件 headline は **`entropyPowerExt` (ℝ≥0∞) 版**。実数版 (`entropyPower : Measure ℝ → ℝ`)
  は `EReal.exp_coe` 変換のため a.c.+有限を要し、完全無条件には**ならない**点を §論点で確定する。

### 核部品 (機械確認済 signature、予測でなく実コード由来)

| # | 名前 | file:line | 仮説 (verbatim 抜粋) | 結論 | 状態 |
|---|---|---|---|---|---|
| 1 | `entropyPowerExt_mono_add_unconditional` | `EPIUncondTruncationLimit.lean:2423` | `(W V) (P) [IsProbabilityMeasure P] (hW hV : Measurable) (hWV : IndepFun W V P) (hW_ac : (P.map W) ≪ volume)` | `entropyPowerExt (P.map (W+V)) ≥ entropyPowerExt (P.map W)` | proof-done `@audit:ok` |
| 2 | `differentialEntropyExt_integrable_of_finite` | `EPIUncondTruncationLimit.lean:2350` | `{μ} (hac : μ ≪ volume) (hne_top : differentialEntropyExt μ ≠ ⊤) (hne_bot : differentialEntropyExt μ ≠ ⊥)` | `Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume` | proof-done `@audit:ok` |
| 3 | `entropyPowerExt_add_ge_finite_ac` | `EPIUncondDispatch.lean:88` | `(X Y) (P) [IsProb] (hX hY : Measurable) (hXY : IndepFun) (hX_ac hY_ac : ≪ volume) (hX_ent hY_ent hW_ent : Integrable (negMulLog∘density) volume)` | `N(X+Y) ≥ N(X) + N(Y)` | proof-done |
| 4 | `entropyPowerExt_singular_add_ge` | `EPIUncondMixedCase.lean:41` | `(X Y) (P) (hX_sing hY_sing : ¬ ≪ volume)` | `N(X+Y) ≥ N(X)+N(Y)` (RHS=0) | proof-done `@audit:ok` |
| 5 | `entropyPowerExt_singular` | `EntropyPowerExt.lean:136` | `{μ} (h : ¬ μ ≪ volume)` | `entropyPowerExt μ = 0` | proof-done `@audit:ok` |
| 6 | `entropyPowerExt_eq_top_of_diffEntExt_top` | `EntropyPowerExt.lean:129` | `{μ} (h : differentialEntropyExt μ = ⊤)` | `entropyPowerExt μ = ⊤` | proof-done `@audit:ok` |
| 7 | `differentialEntropyExt_of_ac` | `EntropyPowerExt.lean:73` | `{μ} (h : μ ≪ volume)` | `differentialEntropyExt μ = (A:EReal) - (B:EReal)` (正部・負部差) | proof-done `@audit:ok` |

注: #5 (`entropyPowerExt_singular`) は docstring (`:134`) によれば**特異枝かつ h=−∞ 枝**を共に `0`
に写す (`differentialEntropyExt_singular` 経由)。ただし「a.c. だが `h=⊥` (負部発散)」を `N=0` に潰す
**named lemma は不在** (in-tree grep 確認、`entropyPowerExt_singular` は `¬ a.c.` 専用) → Phase 0
在庫項。

### import 構造 (機械確認済、cycle なし)

- `EPIUncondTruncationLimit` も `EPIUncondDispatch` も consumer 0 の leaf、相互 import なし。
- `EPIUncondTruncationLimit` は `EPIUncondMonotone`→`EPIUncondMixedCase` 経由で singular 補題を
  transitively 保持。
- ⇒ 新 file **`EPIUncondDispatchFull.lean`** は `import EPIUncondDispatch` (#3 finite_ac 用) +
  `import EPIUncondTruncationLimit` (#1 gateway 用) で cycle なし、両者経由で MixedCase の singular
  補題 (#4/#5) も入る。`InformationTheory.lean` への import 登録を Phase 3 で明記
  (現状 `EPIUncondDispatch` :242 / `EPIUncondTruncationLimit` :245 登録済、新 file は :245 直後に追記)。

---

## Phase 0 — 在庫 gate (EReal exp 境界値 + RHS 確定補助の在庫指示) 📋

proof-log: no (調査のみ)。**この Phase が柱 B (case-1 split) の GO/NO-GO gate**。
`mathlib-inventory` サブエージェントに **structured per-lemma output** (file:line / 完全 signature /
`[...]` 前提 verbatim / 結論形 verbatim) で委任する。**予測値は書かず、確認できないものは「要調査」マーク**。

- [ ] **`entropyPowerExt = EReal.exp (2·differentialEntropyExt)` の ⊤/⊥ 対応** (柱 B の各 sub-case で
  RHS の値 ⊤/N単独/0 を確定するのに必須、予測値禁止):
  - `EReal.exp_top` (`exp ⊤ = ⊤`)、`EReal.exp_bot` (`exp ⊥ = 0`)、`EReal.exp_coe`
    (`exp ↑x = ENNReal.ofReal (Real.exp x)`)、`EReal.exp_monotone` ([gcongr]) を file:line + verbatim 抽出。
  - `EReal.mul_top_of_pos` / `EReal.mul_bot_of_pos` (`2·⊤=⊤` / `2·⊥=⊥`) の verbatim (in-tree
    `entropyPowerExt_eq_top_of_diffEntExt_top` / `entropyPowerExt_singular` が既に使用、出所確認)。
- [ ] **RHS 確定補助 lemma の在庫 (柱 B の核、不在なら自作量を見積る)**:
  - **`differentialEntropyExt μ = ⊤ → entropyPowerExt μ = ⊤`** = #6 既存 (`:129`)。**確認済、自作不要**。
  - **`differentialEntropyExt μ = ⊥ → entropyPowerExt μ = 0`** = **named lemma 不在**
    (`entropyPowerExt_singular` は `¬ a.c.` 専用、a.c. かつ `h=⊥` を覆わない)。`EReal.exp_bot` +
    `EReal.mul_bot_of_pos` の 2 行で genuine に立つ見込み。**在庫項**: 同型 lemma が既にあるか grep +
    無ければ柱 B の helper として `entropyPowerExt_eq_zero_of_diffEntExt_bot` を新規 (~3 行) と見積る。
  - **`differentialEntropyExt μ ≠ ⊤ ∧ ≠ ⊥ ∧ a.c. → Integrable (negMulLog∘density)`** = #2 既存
    (`differentialEntropyExt_integrable_of_finite`、`:2350`)。**確認済、自作不要**。
- [ ] **case-1 split の `h(X+Y) ≠ ⊥` 導出ルートの在庫** (撤退ライン L-Endgame-2-α の事前確認):
  有限 sub-case (h(X),h(Y),h(X+Y) 全有限) で `h(X+Y) ≠ ⊥` を bridge #2 に渡すために要する。候補ルート:
  (a) gateway 単調性 `differentialEntropyExt_mono_add_unconditional` (`:2399`、`h(X) ≤ h(X+Y)`) +
  `h(X) ≠ ⊥` (sub-case 仮定) で `h(X+Y) ≥ h(X) > ⊥`、(b) 直接 by_cases。**在庫項**: gateway 単調性の
  EReal 版 `differentialEntropyExt_mono_add_unconditional` の signature を verbatim 抽出し、(a) が
  `lt_of_lt_of_le` で立つか確認 (`hX_ac` が前提に要る点 — case 1 で X a.c. ゆえ充足)。
- [ ] **finite_ac (#3) の 3 finite-entropy precondition を bridge #2 で全供給できるか** の verbatim 検算:
  #3 は `hX_ent hY_ent hW_ent` を取る。有限 sub-case (3 項全有限) では各々 #2 で供給 (`hX_ac`/`hY_ac`/
  `h(X+Y) a.c.` + 各 `≠⊤`/`≠⊥`)。**在庫項**: `X a.c. ∧ Y 特異でない (= 両 a.c.) ⟹ X+Y a.c.` の
  Mathlib lemma (`IndepFun.map_add_eq_map_conv_map` + `conv_absolutelyContinuous`、MixedCase:49 で既使用)
  を verbatim 抽出 (`h(X+Y) a.c.` を bridge #2 の `hac` に渡すため)。

### Phase 0 撤退ライン

- **L-Endgame-0-α** (RHS 確定補助 不在): `differentialEntropyExt = ⊥ → entropyPowerExt = 0` が
  `EReal.exp_bot` だけで 1 行展開できず、`differentialEntropyExt` の `irreducible_def` 展開で詰まる →
  `differentialEntropyExt_of_ac` (#7) + `EReal.exp_bot` の合成 helper を **新 file 内 private** で
  立てる (~5 行、`@audit:ok` 想定)。これは Mathlib 壁でなく plumbing。
- **L-Endgame-0-β** (在庫 NO-GO 兆候): gateway 単調性が `differentialEntropyExt` (EReal) でなく
  `entropyPowerExt` (ℝ≥0∞) 版しか公開されておらず、`h(X+Y) ≠ ⊥` の EReal-level 導出に使えない →
  `entropyPowerExt` 版から `differentialEntropyExt` の不等式を逆算する経路を再評価 (EReal.exp 単射性
  `EReal.exp_lt_exp` 等の在庫を追加調査)。**確認済**: EReal 版 `differentialEntropyExt_mono_add_unconditional`
  (`:2399`) は公開済ゆえ本撤退ライン不発の見込み (Phase 0 で verbatim 再確認)。

---

## Phase 1 — 柱 A: singular-case rewire (case 2 / case 2 対称) 📋

proof-log: yes。skeleton-driven: 補題を `:= by sorry` で先に立て typecheck → 1 sorry ずつ fill。

新 file `EPIUncondDispatchFull.lean` (namespace `InformationTheory.Shannon`、`open MeasureTheory
Real ProbabilityTheory` + `EntropyPowerInequality`) に以下を立てる。

- [ ] **`entropyPowerExt_mixed_add_ge_uncond`** (case 2: X a.c. ∧ Y 特異)。
  - signature: `(X Y) (P) [IsProbabilityMeasure P] (hX hY : Measurable) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_sing : ¬ (P.map Y) ≪ volume)`、結論 `N(X+Y) ≥ N(X)+N(Y)`。
  - proof: `entropyPowerExt_singular hY_sing` で `N(Y)=0` → `RHS = N(X) + 0 = N(X)` (`add_zero`)。
    gateway #1 `entropyPowerExt_mono_add_unconditional X Y P hX hY hXY hX_ac` で `N(X+Y) ≥ N(X)` を出し
    closure。**integrability 8 本 + finite-entropy 2 本除去**、仮説は `hX hY hXY hX_ac hY_sing` のみ。
- [ ] **`entropyPowerExt_mixed_add_ge_symm_uncond`** (case 2 対称: Y a.c. ∧ X 特異)。
  - signature: `... (hY_ac : (P.map Y) ≪ volume) (hX_sing : ¬ (P.map X) ≪ volume)`、結論同上。
  - proof: gateway #1 を `W=Y, V=X` で呼ぶ (`hWV` は `hXY.symm`) → `N(Y+X) ≥ N(Y)`。`add_comm` で
    `P.map (fun ω => Y ω + X ω) = P.map (fun ω => X ω + Y ω)` を整形 (`congrArg (P.map ·)` +
    `funext` の `add_comm`)、`entropyPowerExt_singular hX_sing` で `N(X)=0` → `RHS = 0 + N(Y) = N(Y)`
    (`zero_add`) で closure。

### Phase 1 撤退ライン

- **L-Endgame-1-α** (`add_comm` reshape 詰まり): `P.map (fun ω => Y ω + X ω)` を
  `P.map (fun ω => X ω + Y ω)` に書換える `congr`/`funext` が `simp` で fire しない →
  `Measure.map_congr` (ae-eq 経由) でなく pointwise `funext (fun ω => add_comm _ _)` を `▸` で適用、
  または gateway #1 を最初から `V=X` で呼んで対称性を吸収。**sorry + `@residual(plan:epi-uncond-dispatch-endgame-plan)`**。
- **L-Endgame-1-β** (gateway 前提不一致): #1 が `IndepFun W V P` を要求し対称版で `hXY.symm` の型が
  `IndepFun Y X P` と合わない → `ProbabilityTheory.IndepFun.symm` の結論形を verbatim 確認し直す
  (Phase 0 在庫に追加)。これは plumbing、壁でない。

---

## Phase 2 — 柱 B: case-1 split (⊤/⊥/有限 sub-case) 📋

proof-log: yes。**endgame 本体**。case 1 (両 a.c.) を `h(X+Y)` / `h(X)` / `h(Y)` の値で split。
RHS = `N(X)+N(Y)`、`N = EReal.exp(2·h)` ゆえ `h=⊤⟹N=⊤`、`h=⊥⟹N=0`。

- [ ] **`entropyPowerExt_add_ge_case1_uncond`** (両 a.c.、finite-entropy 前提なし)。
  - signature: `(X Y) (P) [IsProbabilityMeasure P] (hX hY : Measurable) (hXY : IndepFun X Y P)
    (hX_ac hY_ac : (P.map X / P.map Y) ≪ volume)`、結論 `N(X+Y) ≥ N(X)+N(Y)`。
  - proof skeleton (各 sub-case を `:= by sorry` で立て typecheck → fill):
    1. **`by_cases differentialEntropyExt (P.map (X+Y)) = ⊤`**: 真なら #6
       `entropyPowerExt_eq_top_of_diffEntExt_top` で `N(X+Y)=⊤`、`le_top` (`⊤ ≥ RHS`) で closure。
    2. `h(X+Y) ≠ ⊤` 下、**`by_cases h(X) = ⊤`**: 真なら gateway #1 で `N(X+Y) ≥ N(X)`、#6 で
       `N(X)=⊤` ⟹ `N(X+Y)=⊤` (squeeze、`le_antisymm`/`top_le_iff`)、RHS の `N(Y)` は `le_top` 側で吸収
       (`N(X+Y)=⊤ ≥ N(X)+N(Y)`)。
    3. **`by_cases h(Y) = ⊤`**: 真なら gateway #1 対称 (W=Y) で `N(X+Y) ≥ N(Y)=⊤` → 同上。
    4. **`by_cases h(X) = ⊥`**: 真なら helper (Phase 0 #2) で `N(X)=0` → `RHS = N(Y)` (`zero_add`)、
       gateway #1 対称で `N(X+Y) ≥ N(Y)`。
    5. **`by_cases h(Y) = ⊥`**: 真なら `N(Y)=0` → `RHS = N(X)`、gateway #1 で `N(X+Y) ≥ N(X)`。
    6. **残 (h(X),h(Y),h(X+Y) 全有限 = ≠⊤∧≠⊥)**: bridge #2
       `differentialEntropyExt_integrable_of_finite` で `hX_ent`/`hY_ent`/`hW_ent` を導出
       (`hX_ac`/`hY_ac`/`h(X+Y) a.c.` + 各 `≠⊤`/`≠⊥`) → #3 `entropyPowerExt_add_ge_finite_ac` 呼出。
       `h(X+Y) ≠ ⊥` は **sub-case 仮定で確定済** (case 4/5 を先に分岐済ゆえ残枝で `h(X) ≠ ⊥` ∧
       `h(Y) ≠ ⊥`)、`h(X+Y) ≠ ⊥` 自体は gateway 単調性 (Phase 0 在庫) `h(X) ≤ h(X+Y)` +
       `h(X) ≠ ⊥` から `lt_of_lt_of_le`、または #2 が `hne_bot` を直接要求するので残枝で確保。
       `h(X+Y) a.c.` は両 a.c. + 独立から convolution 保存 (Phase 0 在庫の Mathlib lemma)。

### Phase 2 撤退ライン

- **L-Endgame-2-α** (有限 sub-case で `h(X+Y) ≠ ⊥` 導出が詰まる): gateway 単調性
  `differentialEntropyExt_mono_add_unconditional` (`h(X) ≤ h(X+Y)`) を使った `h(X)≠⊥ ⟹ h(X+Y)≠⊥` が
  `lt_of_lt_of_le`/`bot_lt_iff_ne_bot` の order 補題で fire しない → `h(X+Y)=⊥ ⟹ h(X)=⊥` の対偶を直接
  立てる helper を新規 (~5 行)。**それでも詰まれば該当 sub-case を `sorry` +
  `@residual(plan:epi-uncond-dispatch-endgame-plan)` で park** し、他 sub-case を先に proof-done に。
  本 sub-case は gateway 単調性が EReal-level で公開済 (`:2399`) ゆえ低リスク。
- **L-Endgame-2-β** (RHS 確定補助 lemma が Mathlib 不在): `h=⊥ ⟹ N=0` 等が `EReal.exp_bot` 単独で
  立たず `differentialEntropyExt` 展開を要する → L-Endgame-0-α と同じ private helper を新 file 内に
  立てる (plumbing、壁でない)。Mathlib に exp 境界値そのものが不在なら (Phase 0 で確認済のはず)
  `EReal.exp` の `irreducible_def` を `simp`/`rw` で展開する自作補題に退避。
- **L-Endgame-2-γ** (case 4/5 の squeeze): `N(X)=⊤` かつ `N(X+Y) ≥ N(X)` から `N(X+Y)=⊤` の
  `top_le_iff`/`le_antisymm` が ℝ≥0∞ で fire しない → `ge_iff_le` + `top_le_iff.mp` の標準形に書換。
  これは ℝ≥0∞ order の plumbing、壁でない。

---

## Phase 3 — 柱 C: 完全無条件 dispatch assembly + #print axioms 検証 📋

proof-log: yes。

- [ ] **`entropyPowerExt_add_ge_unconditional`** (完全無条件、`hX hY hXY` のみ)。
  - signature: `(X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (hX hY : Measurable)
    (hXY : IndepFun X Y P)`、結論 `entropyPowerExt (P.map (X+Y)) ≥ entropyPowerExt (P.map X) +
    entropyPowerExt (P.map Y)`。**precondition 21 → 0**。
  - proof: 4 枝 `by_cases (P.map X ≪ volume)` × `by_cases (P.map Y ≪ volume)`:
    - 両 a.c. → 柱 B `entropyPowerExt_add_ge_case1_uncond`。
    - X a.c. ∧ Y 特異 → 柱 A `entropyPowerExt_mixed_add_ge_uncond`。
    - Y a.c. ∧ X 特異 → 柱 A 対称 `entropyPowerExt_mixed_add_ge_symm_uncond`。
    - 両特異 → #4 `entropyPowerExt_singular_add_ge`。
- [ ] **`#print axioms entropyPowerExt_add_ge_unconditional`** = `[propext, Classical.choice,
  Quot.sound]` (sorryAx-free) を機械確認。`by_cases (≪ volume)` の `Classical.dec` は `Classical.choice`
  と同列で許容 (sorryAx ではない、L-Endgame-3-α)。
- [ ] `InformationTheory.lean` に `import InformationTheory.Shannon.EPIUncondDispatchFull` を
  `EPIUncondTruncationLimit` (:245) 直後に追記。
- [ ] **独立 honesty-auditor 起動** (新規 declaration 群を導入、ただし本 plan の新 declaration は全て
  gateway delegation で own sorry 0 を目標。仮に sub-case を park して `sorry`+`@residual` を残した
  場合は CLAUDE.md 必須)。dispatch の honesty (退化定義悪用していないか、case3 の vacuous 達成でないか、
  4 枝の delegation 先が genuine か) を独立検証。

### Phase 3 撤退ライン

- **L-Endgame-3-α** (`Classical.choice` 混入): `by_cases (P.map X ≪ volume)` が `Decidable` を要し
  classical で組むと axioms に `Classical.choice` が増える → propext/Quot.sound と同列で**許容**
  (sorryAx ではない、honest)。既存 dispatch skeleton も同構造で `[propext, Classical.choice,
  Quot.sound]` ゆえ問題なし。
- **L-Endgame-3-β** (柱 B 未完で transitive sorry 残存): 柱 B の有限 sub-case が L-Endgame-2-α で
  park された場合、assembly は transitive sorry を消費 → **honest 部分達成として commit**
  (`entropyPowerExt_add_ge_unconditional` の docstring に「case-1 有限 sub-case は本 plan で closure
  予定、他 3 枝は genuine」明示、`@residual(plan:epi-uncond-dispatch-endgame-plan)`)。無条件構造
  (4 枝 dispatch) は達成、完全 sorryAx-free は柱 B closure 後。

---

## Phase 4 — 柱 D: headline 命名 + 親 Phase 5 同期 📋

proof-log: yes。

- [ ] **拡張版 headline 命名**: 柱 C の `entropyPowerExt_add_ge_unconditional` が**真の無条件 EPI**
  (ℝ≥0∞ 版、`hX hY hXY` のみ)。`_unconditional` 命名は precondition 21→0 ゆえ name-laundering で
  **ない** (CLAUDE.md)。
- [ ] **実数版 headline の論点確定 (⚠ 重要)**: 親 Phase 5 の方針は新名
  `entropy_power_inequality_unconditional` (ℝ版) + 旧 `entropy_power_inequality` corollary 残置。
  **しかし実数版 `entropyPower : Measure ℝ → ℝ` は `entropyPowerExt μ = ENNReal.ofReal (Real.exp
  (2·h μ))` (`entropyPowerExt_of_ac_integrable`) の変換に a.c.+有限を要する** (`EReal.exp_coe` は
  finite EReal でしか ℝ 値に落ちない、`h=±∞` で `⊤`/`0` は ℝ で表現不可)。
  ⇒ **真の無条件 headline は `entropyPowerExt` (ℝ≥0∞) 版のみ**。実数版は a.c.+有限の corollary
  (`entropy_power_inequality_of_ac`、`EPIUncondDispatch.lean:249`、proof-done) に**留まる**。
  - 本 plan は実数版を `_unconditional` と**命名しない** (a.c.+有限 precondition を持つため name
    laundering)。既存 `entropy_power_inequality_of_ac` が実数版の honest 到達点で、本 plan は
    新規実数版 headline を作らず ℝ≥0∞ 版 `entropyPowerExt_add_ge_unconditional` で締める。
- [ ] **親 Phase 5 / sub-plan 表 / DAG を本 plan に同期** (子 SoT、同コミット対象): 親 Phase 5 を
  「gateway 経由 dispatch endgame」へ改稿、sub-plan 表に S4-endgame 行追加、DAG 末尾を本子接続へ。
- [ ] **facts 台帳 `epi-facts.md` 同期**: 「無条件 dispatch headline は 21 precondition」行を、本 plan
  完成後に「`entropyPowerExt_add_ge_unconditional` が `hX hY hXY` のみで sorryAx-free」へ訂正
  (`#print axioms` 再導出コマンド付き、commit hash 更新)。

### Phase 4 撤退ライン

- **L-Endgame-4-α** (実数版無条件を要求された場合): ユーザーが実数版 `_unconditional` を要求 →
  実数版は `h=±∞` を ℝ で表現できないため**真の無条件は型として不可能**であることを論点として
  返す (ℝ≥0∞ 版が唯一の完全無条件、実数版は a.c.+有限 corollary が honest 限界)。これは設計上の
  論点であり撤退でなく、親方針 (実数版 `_unconditional` 新名) との不整合を子 SoT で訂正する。

---

## 撤退ライン共通規律

全 Phase 共通禁止 (CLAUDE.md 検証の誠実性): `Prop := True` placeholder / 結論型≡仮説型 `:= h`
循環 / load-bearing `*Hypothesis` predicate に核を bundle / **退化定義悪用** (特に case3 の `N=0`
vacuous 達成 / a.c. 判定の常時 false 倒し)。撤退口は `sorry` +
`@residual(plan:epi-uncond-dispatch-endgame-plan)` (本 plan で closure)。新規 `sorry`+`@residual`
導入時は独立 honesty-auditor 起動 (Phase 3 step)。

**本 plan の特徴**: 全 declaration が既存 proof-done gateway/bridge への **delegation** で own sorry 0
を目標 (新規 Mathlib 壁を作らない)。詰まるのは plumbing (order 補題 / EReal exp 展開 / `add_comm`
reshape) のみで、いずれも壁でなく self-build で閉じる見込み (Phase 0 在庫で確認)。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。決着済 entry は削除。

1. **2026-06-08 起草**: parent Phase 5 (S4 = assembly) の headline wire endgame として起草。
   S5 (method-Y full gateway) が 2026-06-08 全 proof-done (`entropyPowerExt_mono_add_unconditional`
   / `differentialEntropyExt_mono_add_unconditional` / bridge `differentialEntropyExt_integrable_of_finite`、
   全 sorryAx-free + (i-a) 非継承、`epi-facts.md` 達成表) を受け、残務 = headline wire を本 plan に集約。
   - **設計**: 既存 21-precondition dispatch skeleton (proof-done、consumer 0 leaf) は**改変せず残し**、
     gateway 経由の完全無条件版を新 file `EPIUncondDispatchFull.lean` に**別建て**。柱 A (singular
     rewire) + 柱 B (case-1 split) + 柱 C (assembly) + 柱 D (命名)。
   - **verbatim 確認済 (予測でなく実コード)**: gateway #1 `entropyPowerExt_mono_add_unconditional`
     (`:2423`、regularity のみ)、bridge #2 `differentialEntropyExt_integrable_of_finite` (`:2350`)、
     case-1 #3 `entropyPowerExt_add_ge_finite_ac` (`:88`、3 finite-entropy)、singular #4/#5。RHS 確定
     補助 #6 `entropyPowerExt_eq_top_of_diffEntExt_top` (`:129`、h=⊤⟹N=⊤) 既存。
   - **在庫マーク (Phase 0 委任、予測値禁止)**: `differentialEntropyExt = ⊥ ⟹ entropyPowerExt = 0`
     の named lemma **不在** (`entropyPowerExt_singular` は `¬ a.c.` 専用、a.c. かつ `h=⊥` を覆わない)
     → 柱 B の helper を ~3 行自作と見積り。`EReal.exp_top`/`exp_bot`/`exp_coe`/`mul_top_of_pos`/
     `mul_bot_of_pos` の verbatim、有限 sub-case の `h(X+Y) ≠ ⊥` 導出ルート、両 a.c.⟹X+Y a.c. の
     Mathlib lemma を在庫委任。
   - **論点 (柱 D)**: 真の無条件 headline は `entropyPowerExt` (ℝ≥0∞) 版のみ。実数版は a.c.+有限を
     要する (`EReal.exp_coe`) ため完全無条件にならず、既存 `entropy_power_inequality_of_ac`
     (proof-done) が honest 限界。親方針 (実数版 `_unconditional` 新名) は子 SoT で訂正対象。

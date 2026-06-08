# EPI 無条件化 W-Y2 — route β' (truncation + monotone-limit) サブ計画

> **Parent**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) §Sub-plan 一覧 S5 (W-Y2)
> **slug**: `epi-uncond-truncation-lsc-plan` (= parent S5 が参照する slug、`@residual(plan:epi-uncond-truncation-lsc-plan)` と一致)。
> **status**: 2026-06-08 起草 (route β' feasibility 評価 + 着手 skeleton)。
> **前提資産**: finite ② `differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite` (`EPIUncondCondEntropyExt.lean:262`、11 regularity 仮説、`@audit:ok`) が proof-done 着地済。

## 進捗

- [x] Phase 0 — feasibility gate ✅ **GO** (2026-06-08、scratch `/tmp/route_beta_phase0.lean` 0 error/0 sorry)。weak-conv 回避確定、`hκ_dens_meas` を唯一の真 gap に局所化 (判断ログ 3)。
- [ ] Phase 1 — skeleton (核 lemma signature を `:= by sorry` で立てる) 📋
- [ ] Phase 2 — truncated W_n 構成 + per-n finite-entropy 単調性供給 📋
- [ ] Phase 3 — n→∞ 極限 (単調収束 / EReal ⊤ 表現で weak-conv LSC 回避) 📋
- [ ] Phase 4 — gateway ⊤ 枝 closure + assembly + 独立 honesty-auditor 📋

## ゴール / Approach

### ゴール

parent S5 (方針 Y) の残課題 = **無限エントロピー a.c. 入力 (`h(W) = ⊤` の a.c.) で gateway 単調性
`entropyPowerExt_mono_add` / その ⊤ 伝播 `differentialEntropyExt_top_of_indep_add` を無条件
(整数 truncation 近似経由) で genuine 着地させる**こと。consumer chain (`EPIUncondMonotone.lean`)
は全て無条件版② `differentialEntropyExt_indep_add_eq_add_klDiv` (i-a、`:80`、sorry 残置) に
transitive 依存しており、これが唯一の RED。finite ② は着地済だが、その 11 regularity 仮説が
無限エントロピー入力では充足されないため、**finite ② を truncation で discharge する**のが本 plan。

### Approach (全体形)

**route β' = truncation + monotone-limit (weak-conv LSC を経由しない)**。

無条件版② の等式 (chain rule) は finiteness-free が **証明不能と確定済**
(`epi-uncond-chainrule-ext-inventory.md`「完了状態」、per-fibre mass 相殺が ℝ≥0∞ で不能)。
よって route β' の **ターゲットは等式②でなく gateway 単調性の ⊤ 枝 (不等式)** に据える
(下記 §1 で確定)。LSC/liminf は `≤` しか出さないので等式を極限で作るのは構造的に困難だが、
⊤ 枝は `h(W) = ⊤ ⟹ h(W+V) = ⊤` という不等式 (`le_top` + antisymm) で、EReal が ⊤ を表現できる
ため極限と相性が良い。

機構は **route T (`EPIInfiniteVarianceTruncation` / `EPIInfiniteVarianceCapstone`、sorryAx-free
CLOSED) の流用**:

1. `W` を `W_n := W | {|W| ≤ n}` (conditioning truncation、`condTrunc` / `truncSet` 流用) で
   compact-support 近似する。各 `W_n` は有限分散・有限エントロピー・a.c.(`cond_absolutelyContinuous`
   保存) を満たし、finite ② or finite-entropy 単調性 (`differentialEntropyExt_mono_add` の有限枝) が
   per-n で立つ。
2. n→∞ で `differentialEntropyExt (P.map W_n) → differentialEntropyExt (P.map W)`。`h(W) = ⊤` の
   ときは `h(W_n) ↑ ⊤` の **単調発散** (truncation を緩めると entropy 増加、有界増加列の ⊤ への発散)
   で、weak-convergence portmanteau を経由しない。route T が in-tree で `tendsto_measure_iUnion_atTop`
   ベースの極限を実証済 (`EPIInfiniteVarianceTruncation.lean:110`)。
3. per-n の単調性 `h(W_n) ≤ h(W_n + V)` (finite-entropy 枝) と `h(W_n) ↑ ⊤` を組み、`h(W_n+V) ≥ h(W_n)
   → ⊤` で `h(W+V) = ⊤`。route T capstone Case 2 (`hent_sum` 非成立 → `entropyPowerExt = ⊤`、`le_top`、
   `EPIInfiniteVarianceCapstone.lean:343`) と同型の「⊤ 枝は EReal ⊤ 表現で trivial に閉じる」を再利用。

**§1-C STALE / §4 sidestep の reconcile** (在庫 `epi-uncond-truncation-lsc-inventory.md` の悲観 verdict を緩める):
- 在庫 §1-C「ℝ workhorse が ±∞ 非表現」は **STALE**: 現行 `differentialEntropyExt : Measure ℝ → EReal`
  (`EntropyPowerExt.lean:59`) は a.c. 枝で正部・負部 EReal 差 `A − B` を取り、`A=⊤,B<⊤ → ⊤` で h=+∞ を
  genuine 表現する (def-fix 済、`@audit:ok`)。在庫の verdict は def-fix 以前の human-judgment で、route β'
  の型障害は解消されている。
- 在庫 §4「平滑が裾を消さない」は **Gaussian smoothing の話で route β' には当たらない**: smoothing
  (`X+√t Z`) は畳み込みで分散 = 和なので heavy-tail を残すが、truncation (`W|{|W|≤n}`) は裾を**切り落とし**
  compact support を作るので有限分散・有限エントロピーを genuine 供給する別機構。route T が同 truncation で
  sorryAx-free closure 済 = この sidestep は実証済。
- 残る genuine wall 候補 `wall:entropy-lsc-weak` (弱収束 LSC、loogle Found 0×5、`loogle-neg` 信頼度高) は
  **weak-convergence ルート専用の壁**。route β' は monotone-limit + EReal ⊤ 表現で weak-conv LSC を回避する
  ため、この wall には当たらない見込み (Phase 0 gate で裏取り)。

## 総合 feasibility 判定

**(B) path 可視 multi-session moonshot** (genuine wall でない、L-Uncond-3-scope 発動不要)。

根拠:
1. route T (同型の truncation + R→∞ + EReal ⊤ 枝) が `wall:epi-infinite-variance-classical` を
   **FALSE WALL と判明させ sorryAx-free closure 済** (`EPIInfiniteVarianceCapstone.lean`、独立監査 PASS)。
   route β' は route T の機構 (条件付き truncation / a.c. 保存 / 単調極限 / ⊤ 枝の `le_top`) を
   `W` 単独 truncation に読み替えて再利用する。
2. ターゲットを等式②でなく ⊤ 枝不等式に据えることで、LSC/liminf の「`≤` しか出ない」制約が
   逆に味方になる (⊤ 枝は `le_top` 一発)。
3. 残る Mathlib gap は「truncated `W_n` の per-n 単調性供給」と「`h(W_n) ↑ h(W)` の極限」で、両方とも
   route T が in-tree template を持つ (Gibbs + DCT + `tendsto_measure_iUnion_atTop`)。

**NO-GO 兆候 (Phase 0 で監視)**: per-n の有限-entropy 単調性が finite ② の `hκ_dens_meas` (joint 密度可測) /
`hκ_KL` (per-fibre KL 有限) を `W_n` で供給できない場合、または `h(W_n) ↑ h(W)` の極限が weak-conv に
退化して `wall:entropy-lsc-weak` に当たる場合。後者が確定したら §撤退ライン L-Uncond-Y-roi で
headline を `entropy_power_inequality_of_ac` (a.c.+有限エントロピー、proof-done) に確定。

## 推奨ターゲット

**gateway 単調性の ⊤ 枝 (`differentialEntropyExt_top_of_indep_add`、`EPIUncondMonotone.lean:153`)、
すなわち無条件版②経由の `entropyPowerExt_mono_add` の RED 解消**。等式② (chain rule) は **採らない**。

確定根拠 (verbatim):
- `EPIUncondMonotone.lean` の consumer chain は `differentialEntropyExt_mono_add` (`:123`) →
  `differentialEntropyExt_top_of_indep_add` (`:153`) → `entropyPowerExt_mono_add` (`:176`)。
  これら **3 つは全て無条件版② (i-a) の transitive sorry のみを継承し、独自 sorry を持たない**
  (`EPIUncondMonotone.lean:117-121` / `:148-152` / `:172-175` の docstring で「sorryAx は (i-a)
  transitive 継承のみ」と機械確認記述)。
- つまり (i-a) = `differentialEntropyExt_indep_add_eq_add_klDiv` (`:80`) を closure すれば 3 つ一括
  proof-done。(i-a) は ① fibre 同定 (genuine) + ③ = ② chain rule の合成で sorry が ② に局所化されている。
- ② の **finiteness-free 等式版は証明不能確定**。よって route β' は「(i-a) を等式で建てる」のでなく、
  **gateway 単調性 (不等式) を truncation 近似で直接建て、無条件版② を bypass する**新ルートを足す。
  具体的には finite ② (or finite-entropy 単調性) を `W_n` に適用 → n→∞ で gateway ⊤ 枝を closure し、
  (i-a) sorry を回避する新 lemma `differentialEntropyExt_top_of_indep_add_truncation` を建てて
  consumer (`entropyPowerExt_mono_add` の ⊤ 入力ケース) を rewire する。

## Phase 0 — feasibility gate (ターゲット確定 + truncation 構成 verbatim 検算) 📋

proof-log: no (調査 + gate のみ、実装着手しない)。**この Phase が GO/NO-GO gate**。

- [ ] **ターゲット signature 確定**: gateway ⊤ 枝の最終形を verbatim 固定。`h(W) = ⊤ ∧ W ⊥ V ∧ W a.c.
  ⟹ h(W+V) = ⊤` (= `differentialEntropyExt_top_of_indep_add` の無条件版)。`hV_ac` 追加要否を
  `EPIUncondMonotone.lean:153` の現 signature と照合 (現状 `hW_top` precondition 付き、これは場合分け
  なので残してよい)。
- [ ] **truncation 構成の verbatim 検算**: route T の `condTrunc` / `truncSet`
  (`EPIInfiniteVarianceTruncation.lean:100/`) は `X+Y` joint truncation。route β' は `W` 単独 truncation
  なので `truncSet1 W n := {ω | |W ω| ≤ n}` 形を新規 or 流用。a.c. 保存 `cond_absolutelyContinuous`
  (`ConditionalProbability.lean`) の signature を verbatim 確認 (`(P.map W_n) ≪ volume` が `W a.c.` から
  出るか)。**予測禁止、Read で確認**。
- [ ] **per-n finite-entropy 単調性の供給可能性**: `W_n` (compact support) が finite ②
  (`differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite`、11 仮説) or 有限枝単調性
  (`differentialEntropyExt_mono_add` の coe 枝) の前提を満たすか検算。特に `hκ_dens_meas` (joint 密度
  可測) / `hκ_KL` (per-fibre KL 有限) / `hX_ne_bot` を `W_n + V` の condDistrib で discharge できるか。
  compact support ⟹ 有限分散 ⟹ Gaussian maxent 上界 `differentialEntropy_le_gaussian_of_variance_le`
  (`DifferentialEntropy.lean:520`) で有限エントロピー、という route T と同じ供給チェーンを確認。
- [ ] **極限 step の weak-conv 回避可否 (最優先)**: `h(W_n) ↑ ⊤` (truncation 緩和で entropy 単調増加)
  を `tendsto_measure_iUnion_atTop` (`EPIInfiniteVarianceTruncation.lean:110`) ベースの単調極限で出せるか、
  それとも `klDiv_le_liminf_of_ae_tendsto` (`EPIG2KLFatouLSC.lean:112`、density a.e. 収束 → liminf bound、
  `@audit:ok`) が要るか。後者は weak-conv でなく **density a.e. 収束**を仮定する特殊版なので
  `wall:entropy-lsc-weak` (弱収束版) には当たらない。**どちらでも weak-conv portmanteau を回避できることを
  確認** = この gate の核心。
- [ ] **Phase 0 撤退**: 極限 step が weak-conv に退化し回避不能なら L-Uncond-Y-roi (下記) を発動、
  headline を a.c.+有限エントロピー版に確定。

## Phase 1 — skeleton 📋

`InformationTheory/Shannon/EPIUncondTruncationLimit.lean` を skeleton で立てる
(skeleton-driven、各 lemma `:= by sorry` + `@residual`)。核 lemma:

```lean
-- W 単独 truncation の構成 + regularity (route T `condTrunc` を W 単独に読み替え)
noncomputable def truncW (P : Measure Ω) (W : Ω → ℝ) (n : ℕ) : Measure Ω :=
  ProbabilityTheory.cond P {ω | |W ω| ≤ n}

-- per-n finite-entropy 単調性: 各 n で h(W_n) ≤ h(W_n + V) を finite ② 経由で建てる
theorem differentialEntropyExt_mono_add_truncW
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume) (n : ℕ) (hn : P {ω | |W ω| ≤ n} ≠ 0) :
    differentialEntropyExt ((truncW P W n).map W)
      ≤ differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω)) := by
  sorry -- @residual(plan:epi-uncond-truncation-lsc-plan)

-- h(W_n) ↑ h(W): truncation 緩和で entropy 単調増加 → 極限 (h(W)=⊤ で ⊤ へ単調発散)
theorem differentialEntropyExt_truncW_tendsto
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hW_ac : (P.map W) ≪ volume) :
    Tendsto (fun n => differentialEntropyExt ((truncW P W n).map W)) atTop
      (𝓝 (differentialEntropyExt (P.map W))) := by
  sorry -- @residual(plan:epi-uncond-truncation-lsc-plan)

-- gateway ⊤ 枝 (無条件): h(W)=⊤ ⟹ h(W+V)=⊤、無条件版② を bypass
theorem differentialEntropyExt_top_of_indep_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    differentialEntropyExt (P.map (fun ω => W ω + V ω)) = ⊤ := by
  sorry -- @residual(plan:epi-uncond-truncation-lsc-plan)
```

- [ ] skeleton を Write し type-check (sorry warning のみ期待)。
- [ ] import 順序 + `InformationTheory.lean` 編入 (新 file)。
- [ ] hidden type-class leak の確認: finite ② が要求する
  `[MeasurableSpace.CountableOrCountablyGenerated α ℝ]` (`EPIUncondCondEntropyExt.lean:306`) が `Z := V`
  (`α := ℝ`) で自動 derive されるか (`ℝ` は countably generated)。leak すれば signature に追加。

## Phase 2 — truncated W_n 構成 + per-n 単調性供給 📋

proof-log: yes (per-n finite-entropy 単調性が route T と同じ Gibbs+maxent チェーンで genuine に立つかが
本 plan の主リスク)。

- [x] **truncW の regularity**: a.c. 保存 (`cond_absolutelyContinuous`.map.trans)、compact support
  (`{|W|≤n}` 条件付け)、有限エントロピー (`hW_ent_Q` genuine: 正部=裾切り + 負部=`hW_negPart_fin`)。commit 28cb110。
- [~] **per-n finite ② 適用** (案 F、判断ログ 4): `differentialEntropyExt_mono_add_truncW` 本体 genuine 配線
  完成 + 残 6 局所 sorry のうち **2 本 genuine** (`hW_ne_bot` / `hκ_logp_int`)、**4 本 sum-marginal crux 残**
  (`hWV_ne_bot` / `h_ac` / `hκ_cross_int` / `hκ_KL`、`@residual(plan:...)`)。signature に regularity 仮説
  `hW_negPart_fin` (B(W)<⊤) 追加 (honesty-auditor PASS = 非 load-bearing)。`hκ_ac` も genuine。
- [ ] **sum-marginal crux 4 本の closure** (Phase 2 後半): `h_ac` (`compProd_map_condDistrib` 配線 ~150 行) /
  `hWV_ne_bot` (route T 負部 lemma の single-component 一般化) / `hκ_cross_int` / `hκ_KL` (downstream)。
- [ ] proof-log に「どの仮説が compact support から自動か / どれを明示供給したか」を記録。

## Phase 3 — n→∞ 極限 (単調収束で weak-conv 回避) 📋

proof-log: yes (極限 step が weak-conv LSC wall を回避できるかが feasibility の分かれ目)。

- [ ] **`h(W_n) ↑ ⊤`**: `h(W)=⊤` のとき truncation 緩和列 `h(W_n)` が ⊤ へ単調発散。`truncW_tendsto` を
  `tendsto_measure_iUnion_atTop` + 単調列の極限で建てる (route T `measure_truncSet_tendsto_one` 流用)。
- [ ] **weak-conv 回避の確認**: この極限が density a.e. 収束 (`klDiv_le_liminf_of_ae_tendsto` 適用可) or
  単調収束のみで閉じ、`MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` (弱収束定義) を
  使わないことを proof で担保。weak-conv を使ったら即 L-Uncond-Y-roi 検討。

## Phase 4 — ⊤ 枝 closure + assembly + 監査 📋

- [ ] **⊤ 枝 assembly**: per-n 単調性 `h(W_n) ≤ h(W_n + V)` + `h(W_n) ↑ ⊤` から `h(W_n + V) ≥ h(W_n) → ⊤`
  で `h(W+V) = ⊤` (`le_top` + 極限)。route T capstone Case 2 (`EPIInfiniteVarianceCapstone.lean:343`、
  `entropyPowerExt = ⊤` を `le_top`) と同型。
- [ ] **consumer rewire**: `entropyPowerExt_mono_add` の無限エントロピー入力ケースを
  `differentialEntropyExt_top_of_indep_add_unconditional` に rewire し、無条件版② (i-a) 依存を ⊤ 枝で
  bypass。有限枝は finite ② / coe 枝で別途。残る (i-a) sorry が真に消えるか
  (`#print axioms entropyPowerExt_mono_add` で sorryAx 確認)。
- [ ] **独立 honesty-auditor 起動** (新規 sorry + @residual / signature 変更を導入するため必須、CLAUDE.md
  「Independent honesty audit」)。truncation 仮説が regularity (非 load-bearing) であること、⊤ 枝の
  `le_top` が退化定義悪用でないことを独立検証。

## 撤退ライン

- **L-Uncond-Y-roi** (route β' が極限 step で weak-conv LSC wall に退化): per-n 単調性は立つが
  `h(W_n) ↑ h(W)` の極限が単調収束で閉じず weak-convergence portmanteau (`wall:entropy-lsc-weak`、
  loogle Found 0×5) を本質的に要求すると確定したら、無限エントロピー入力の救済を断念。headline を
  `entropy_power_inequality_of_ac` (両 a.c. + 両有限エントロピー、proof-done) に確定する。これは方針 X
  より strictly 強い honest 中間形 (特異入力の退化トラップ除去は無条件で保たれる、parent 発見 1+2)。
  撤退口は `sorry + @residual(wall:entropy-lsc-weak)` を極限 lemma に残し、最終 gateway は有限エントロピー
  signature で genuine 着地。**`hX_ent`/`hW_ent` は regularity precondition で load-bearing でない**
  (CLAUDE.md 判定軸「前提条件か証明の核心か」→ 前者)。

- **L-WY2-trunc** (per-n 単調性が truncation で供給できない): `truncW P W n` の condDistrib で finite ②
  の `hκ_dens_meas` / `hκ_KL` が discharge できない場合、conditioning truncation でなく別構成
  ([-n,n] への restriction + 再正規化、Gaussian convolution 後 truncation 等) を 1-2 案試す。route T が
  conditioning truncation で同種供給を実証済なので発動可能性は低い。

- **共通**: 詰まったら signature を結論形に保ち `sorry + @residual(plan:epi-uncond-truncation-lsc-plan)`
  (or wall 化が確定したら `@residual(wall:entropy-lsc-weak)` に昇格)。`*Hypothesis` predicate に核を
  bundling する撤退は禁止 (honesty defect)。`_unconditional` 命名は threaded regularity precondition が
  残る間は name-laundering ゆえ慎重に (有限エントロピー版に確定したら命名から `_unconditional` を外す)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除、active な判断のみ残す。

1. **ターゲットを等式②でなく gateway ⊤ 枝に確定 (2026-06-08)**: 無条件版② chain rule の finiteness-free
   等式は **証明不能と確定済** (`epi-uncond-chainrule-ext-inventory.md`「完了状態」、per-fibre mass 相殺が
   ℝ≥0∞ で不能、proof-pivot-advisor 裏取り)。LSC/liminf は `≤` しか出さず等式を極限で作れないため、route β'
   は等式②を放棄し gateway 単調性の ⊤ 枝 (不等式) を truncation 近似で直接建てて無条件版② を bypass する。
   consumer chain (`EPIUncondMonotone.lean`) は全て (i-a) の transitive sorry のみ継承するので、⊤ 枝の
   無条件 closure で gateway が proof-done 昇格する (有限枝は finite ② / coe 枝で別途)。

3. **Phase 0 gate = GO、risk を `hκ_dens_meas` に局所化 (2026-06-08)**: scratch `/tmp/route_beta_phase0.lean`
   (0 error/0 sorry) で 3 核心問いを機械裏取り。**Q1 (核心)**: Fatou lift `A_W ≤ liminf A_{W_n}` が density a.e.
   収束のみから fire (`klDiv_le_liminf_of_ae_tendsto` `EPIG2KLFatouLSC.lean:112` と完全同型、`klFun`→`negMulLog`
   差替のみ、両者 continuous)。`A_W=⊤ ⟹ liminf A_{W_n}=⊤` を `top_le_iff` で確定 = ⊤ 枝 LSC が weak-conv 抜きで
   立つ ⇒ `wall:entropy-lsc-weak` 回避確定 (L-Uncond-Y-roi 発動不要)。**Q2**: a.c. 保存 = `cond_absolutelyContinuous`
   (`ConditionalProbability.lean:183`、`[IsProbabilityMeasure P]` のみ) + `.map hW |>.trans hW_ac` の 2 行、W 単独
   truncation で十分 (route T joint `truncSet` 不要)。**Q3**: type-class leak 解消 (`CountableOrCountablyGenerated ℝ ℝ`
   が `infer_instance` 自動)。finite ② 11 仮説の W_n discharge は `hκ_dens_meas` (joint 密度可測
   `Measurable (fun p : α×ℝ => (condDistrib X Z μ p.1).rnDeriv vol p.2)`、loogle Found 0、Mathlib 不在) のみ **HARD**、
   残 10 は OK/medium。**finite ② は in-tree consumer 0** ゆえ route β' Phase 2 が 11 仮説の初実地 discharge =
   `hκ_dens_meas` が Phase 2 主リスク (撤退口 `sorry + @residual(plan:...)`、wall 化確定なら昇格)。

2. **在庫 §1-C STALE / §4 sidestep の reconcile (2026-06-08)**: 在庫 `epi-uncond-truncation-lsc-inventory.md`
   の悲観 verdict (L-Uncond-3-scope 推奨) は **def-fix 以前 + Gaussian smoothing 前提**。§1-C「ℝ workhorse が
   ±∞ 非表現」は現行 EReal def (`A−B` 差で h=+∞ を ⊤ 表現) で STALE。§4「平滑が裾を消さない」は smoothing 専用
   で、truncation (裾を切り落とす別機構) には当たらない。route T が同 truncation で sorryAx-free closure 済 =
   sidestep 実証。残る `wall:entropy-lsc-weak` は weak-conv ルート専用で、monotone-limit + EReal ⊤ 表現で回避
   見込み (Phase 0 gate で裏取り)。⇒ 在庫の悲観は緩み、総合判定 (B) path 可視 moonshot。

4. **案 F = 部分的成功、sum-marginal crux 4 本が残存 (2026-06-08)**: #3 `differentialEntropyExt_mono_add_truncW`
   に regularity 仮説 `hW_negPart_fin` (B(W)<⊤) を 1 本追加し残 6 局所 sorry を closure 試行。**2 本 genuine**
   (`hW_ne_bot`: 正部=裾切り `negMulLog_le_one_sub_self` + 負部 `hW_negPart_fin` の `negMulLog_mul` 分解、
   `hκ_logp_int`: fibre が `Q.map W` の平行移動という構造で還元)。**4 本は sum-marginal `Q.map(W+V)` 解析で
   ブロック** (`hWV_ne_bot` / `h_ac` / `hκ_cross_int` / `hκ_KL`)。当初仮定の修正: advisor 案 F の「全部 `hae`
   経由で B(W_n) に還元」は per-fibre が `Q.map W` の平行移動である項にしか効かず、sum marginal 参照項
   (mixture/convolution) は還元不能。honesty-auditor verdict = **all OK**: `hW_negPart_fin` = regularity
   (core-reconstruction FAIL = 非 load-bearing)、4 residual の `plan:` classification 妥当 (wall: 化不要)。
   closure ルート (auditor 確認): `h_ac` は `compProd_map_condDistrib` + `condDistrib_ae_eq_of_measure_eq_compProd`
   (Mathlib 実在) 配線 ~150 行、`hWV_ne_bot` は route T 負部 lemma `integrable_negPart_negMulLog_map_condTrunc_sum`
   (`EPIInfiniteVarianceTruncation.lean:600`) を **single-component 一般化** (現状両成分 entropy 要求だが
   Jensen averaging は片成分の law 上ゆえ片方の finite entropy で足る = 一般化で `hWV_ne_bot` アンブロック +
   EPI truncation family 再利用可)、`hκ_cross_int` は cross-entropy domination、`hκ_KL` は `h_ac`+`hκ_cross_int`
   の downstream (`klDiv_ne_top`)。⇒ Phase 2 後半 = この 4 本の dispatch。
   注: `wall:entropy-lsc-weak` は撤退ライン予約 slug、Phase 0 で回避確定 = code 未登録は設計通り、plan_lint
   STALE は既知の誤検出。

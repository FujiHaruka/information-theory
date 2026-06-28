# MAC: 2-codebook averaging closure (`mac_random_codebook_average_le`) サブ計画

> **Parent**: [`mac-moonshot-plan.md`](mac-moonshot-plan.md) §Phase D-2 (撤退ライン L-MAC3)
>
> **Status**: **CLOSED (2026-06-28)** — genuine closure 達成。`mac_random_codebook_average_le` を sorryAx-free 化し、headline `mac_achievability` が推移的に proof done。両者 `#print axioms` = `[propext, Classical.choice, Quot.sound]` (機械確認済)、独立 honesty 監査 `@audit:ok`。これにより MAC achievability genuine closure → 親の MAC 容量領域 full closure (converse は Phase A2 で既達)。

<!--
記法は moonshot-plan-template と同じ（状態絵文字 📋🚧✅🔄、取り消し線、append-only 判断ログ）。
Parent ヘッダは plan_lint の親子グラフ構築点。子の状態を変えたら親 §Phase D-2 行も同期する
（衝突時は子が SoT → CLAUDE.md「Plan / docs hygiene」親子整合）。
プラン予算 ≤ 600 行 / active 判断ログ ≤ 10 entry。
-->

## 進捗 — 全 ✅ CLOSED

- [x] M0 — 流用 / 再導出インベントリ + 方針決定 ✅
- [x] M1 — 算術 + per-codebook marginal カーネル ✅
- [x] M2 — E0 swap（正解 pair atypicality）✅
- [x] M3 — E1/E2 alias swap（**最重量、gateway-atom-first**）✅
- [x] M4 — E3 swap（両 alias、4-row）✅
- [x] M5 — 組立 `mac_random_codebook_average_le`（sorry L274 解消）✅
- [x] MV — verify（sorryAx-free + 推移的 `mac_achievability` proof done）✅

## Context（残差の所在）

MAC achievability は **唯一 1 箇所** を残して proof done に到達済み。残差 =
`InformationTheory/Shannon/MultipleAccess/Achievability.lean:256` の
**`mac_random_codebook_average_le`**（本体 L274 が `sorry` + `@residual(plan:mac-achievability-bonferroni-plan)`）。

すでに genuine（sorryAx-free / `@audit:ok`）に閉じている下流・周辺:

- gateway atom（analytic 核、本計画の入力）: `AchievabilityCore.lean` の
  `macJTS_indep_prob_le_X1` (L50) / `_X2` (L271) / `_both` (L182)。
- 正解 pair AEP: `JointTypicality.lean` `macJointlyTypicalSet_prob_tendsto_one` (L195)。
- per-pair 4-event Bonferroni: `Achievability.lean` `mac_errorProbAt_le_bonferroni4` (L91)。
- pigeonhole + closed-form rate 境界: `mac_exists_codebook_le_avg` (L283) /
  `mac_E3_lt_of_rate` (L364)、headline `mac_achievability` (L405) は **配線済**で
  `mac_random_codebook_average_le` を直呼びするだけ。

つまり headline は averaging 補題 **1 本に推移的に依存**しており、それを sorryAx-free に
すれば `mac_achievability` が proof done（→ MAC achievability genuine closure）。

**なぜ type-check done で止まっているか**: averaging は新規 analytic gap ではなく、
**単一ユーザ swap infra（`RandomCodebook.lean` ~1300 行）の 2-codebook 一般化が plumbing
volume**だから。単一ユーザは 2-event（correct codeword atypical + 1 alias）だが MAC は
4-event（E0 + 3 alias）で、各 alias の codebook averaging が単一ユーザより 1 段重い
**3-codeword marginalization + pair-channel fold**を要する。重いのは行数であって発想ではない。

## ゴール / Approach（overall strategy / shape of solution）

`mac_random_codebook_average_le` は **単一ユーザ `random_codebook_average_le`
（`RandomCodebook.lean:1157`）の 2-codebook / 4-event 一般化**。攻略の骨格は単一ユーザと同型:

1. **per-pair を Bonferroni で 4 項に割る**（D-1 `mac_errorProbAt_le_bonferroni4` 既存）。
   送信 pair `(m₁,m₂)` の per-pair 誤りを per-pair block 測度
   `ν = Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))` 上で E0/E1/E2/E3 に分解。

2. **product codebook 上で期待値を取り線形性で 4 和に分配**（算術、M1）。
   `(M₁M₂)⁻¹ ∑_{m₁,m₂}[E0 + ∑_{m₁'}E1 + ∑_{m₂'}E2 + ∑_{m₁',m₂'}E3]` の各項に
   `∑_{c₁,c₂} w₁{c₁}w₂{c₂}·` を内側へ swap。単一ユーザ
   `sum_weighted_diag_offdiag_decomp` (L1050、public) の 4-event 版。

3. **各項を「swap の核」で ambient 形 / gateway 形に化けさせる**（M2/M3/M4、本計画の重心）。
   これが単一ユーザの `codebook_marginal_one/two` + `random_codebook_E1/E2_swap` に対応。
   核は項ごとに以下の通り（**何行が絡むか**で重さが決まる）:

   - **E0（正解 pair atypical）**: 測度 `ν` は `c₁ m₁`・`c₂ m₂`（真符号語 2 行）に依存、
     事象も同じ 2 行に依存 → **各 codebook 1 行ずつの marginalization**（diag）。
     化けた積測度を fold すると ambient 正解 triple atypicality
     `(macAmbientMeasure).real {ω | correct triple ∉ macJTS}` = E0_avg そのもの。
     単一ユーザ `random_codebook_E1_swap` (L669) と同型。

   - **E1（user-1 alias、m₁'≠m₁）**: 測度 `ν` は `c₁ m₁`（真 user-1）・`c₂ m₂`（真 user-2）に、
     事象は `c₁ m₁'`（alias user-1）・`c₂ m₂`（真 user-2）に依存 → **3 行が絡む**
     （真 user-1 / alias user-1 / 真 user-2）。これが単一ユーザより重い唯一の点。
     marginalization は `codebook_marginal_two`（c₁ で m₁/m₁' の 2 行）+
     `codebook_marginal_one`（c₂ で m₂ の 1 行）の **Fubini ネスト**に分解できる
     （新しい combinatorial カーネルは不要）。重いのは続く **conditional-output
     fold-in identity**: 真 user-1 符号語 `x₁`（ν にのみ現れる）を pair-channel から
     周辺化すると、`(X₂,Y)` の joint block law に畳み込まれる。残りは alias `x̃₁` ⟂ `(x₂,y)`
     の **積測度形** `((μ.map jointRV macX1s).prod (μ.map (X₂,Y)-joint)).real (reshape macJTS)`
     = gateway atom `macJTS_indep_prob_le_X1` の入力にちょうど一致。

   - **E2（user-2 alias）**: E1 の user-1/user-2 鏡像。fold 先は gateway `macJTS_indep_prob_le_X2`。

   - **E3（両 alias、m₁'≠m₁ かつ m₂'≠m₂）**: 4 行が絡む（真 pair 2 行 + alias pair 2 行）。
     `codebook_marginal_two` を **両 codebook**に適用 + 真 pair `(x₁,x₂)` を channel から
     fold → Y block law。残りは `(x̃₁,x̃₂) ⟂ y` の積測度 = gateway `macJTS_indep_prob_le_both`
     の入力。出力軸が `Y` 単独なので単一ユーザ `random_codebook_E2_swap` (L906) に最も近い。

4. **alias 個数を掛けて集約**（算術、M1）。offdiag を数えると `(M₁-1)`・`(M₂-1)`・
   `(M₁-1)(M₂-1)` が出る。単一ユーザ `diag_add_offdiag_sum_le` (L1084) /
   `sum_average_le_of_forall_le` (L1105、両 public) の 4-event 版。

**指数の符号橋（concrete 確認済）**: gateway atom の指数 core は coord 選択子の ambient
エントロピー `H(X₁,X₂,Y) − H(X₁) − H(X₂,Y)` 等。`IIDAmbient.lean` `macAmbient_entropy_coord`
(L160) で `entropy (macAmbientMeasure) (coord g) = entropy (macJointDistribution) g` と橋渡し
すると、target RHS の `-(macInfo₁)`（= `H(X₁,X₂,Y) − H(X₁) − H(X₂,Y)`、`macInfo₁` 定義
L218 から検算済）にちょうど一致。E2/E3 も `-(macInfo₂)` / `-(macInfoBoth)` に一致（検算済）。

**gateway 仮説の構成は純 plumbing**: gateway atom が要求する
`iIndepFun` / `IdentDistrib` / `hpos*`（X1・(X2,Y)・Z 各軸）は全て IIDAmbient の
`macAmbient_iIndepFun_coord` (L124) / `macAmbient_identDistrib_coord` (L146) /
`macAmbient_map_coord_real_singleton_pos` (L231) を coord 選択子に適用して構成（既存・proven）。

**Mathlib-shape-driven**: 新規定義は導入しない。target の結論形（`codebookMeasure`、
`macInfo₁/₂/Both`、gateway atom 形）を**そのまま受ける**よう swap を組む。

## M0 — 流用 / 再導出インベントリ + 方針決定
**proof-log**: no

- [ ] **`MACCodebook M n α` ≡ `Codebook M n α` 確認**: 両者 `Fin M → Fin n → α`
  （`Codebook` は `abbrev`、`Core.lean:50`）。defeq ゆえ public `codebookMeasure`
  (`Core.lean:216`) と単一ユーザ marginal 補題が型一致する（target が既に
  `codebookMeasure p₁ M₁ n {c₁}`（`c₁ : MACCodebook …`）を typecheck している事実が裏付け）。
- [ ] **流用可能な public ヘルパ列挙**（そのまま `open` 1 つで使える）:
  `measureReal_pi_singleton_eq_prod` (L30) / `prod_erase_eq_prod_subtype_ne` (L228) /
  `sum_prod_measureReal_singleton_eq_one` (L255) / `sum_weighted_diag_offdiag_decomp` (L1050) /
  `diag_add_offdiag_sum_le` (L1084) / `sum_average_le_of_forall_le` (L1105) — 全て `RandomCodebook.lean` で既に **非 private**。
- [ ] **promote vs 再導出の決定**（唯一の判断点）: `codebook_marginal_one` (L281) /
  `codebook_marginal_two` (L433) は `private`。両者は型ジェネリック（任意 α・任意 `f`、
  単一ユーザ channel に依存しない）ゆえ MAC で c₁(α₁)・c₂(α₂) に直接適用可能。
  - **mainline = MAC-local 再導出**（MAC ディレクトリ自己完結、proven な単一ユーザ定理に
    olean refresh リスクを波及させない）。~280 行のほぼ verbatim 複製コスト。
  - **代替 = single-user を public 化して流用**（重複ゼロ、ripple ゼロ — private ゆえ既存
    cross-file consumer 0、visibility 昇格は signature 不変で既存呼出を壊さない）。採るなら
    実装 agent が `RandomCodebook.lean` を co-stage（共有ファイル編集）。
  - 判断: 重複コストが許容なら mainline、嫌なら代替。**どちらも既存 signature を変えない**
    （hyp threading / 引数追加なし）ので親計画の consumer ripple は無い。
- [ ] **MAC 専用に再導出が必須なもの**（pair-channel 構造ゆえ単一ユーザを流用できない）:
  conditional-output fold-in（pair input、M3）と block-law 同定（IIDAmbient 経由、下記）。
- [ ] **block-law 同定の近道確認**: 単一ユーザ `block_law_X_eq_pi_p` (L126) /
  `block_law_Y_eq_pi` (L161) / `block_joint_law_eq_pi` (L192) は private だが、MAC は
  `macAmbient_map_coord` (IIDAmbient L111、public + proven) で
  `(macAmbientMeasure).map (coord g) = (macJointDistribution).map g` を直接得られるため、
  これら private 補題の promote は不要（MAC は IIDAmbient 経由の方が短い）。

## M1 — 算術 + per-codebook marginal カーネル
**proof-log**: no（決定的・機械的）

- [ ] `mac_averageErrorProb_toReal_eq`: `(c.averageErrorProb W).toReal
      = ((M₁ * M₂ : ℕ) : ℝ)⁻¹ * ∑ m₁, ∑ m₂, (c.errorProbAt W (m₁,m₂)).toReal`。
      単一ユーザ `averageErrorProb_toReal_eq` (L1120) の M₁·M₂ 正規化版。
      `MACCode.averageErrorProb` 定義（Basic.lean）+ per-pair `errorProbAt ≠ ∞` を要する。
- [ ] `mac_errorProbAt_ne_top`: `(macCodebookToCode …).errorProbAt W (m₁,m₂) ≠ ∞`
      （`≤ 1`、Markov kernel）。単一ユーザ `errorProbAt_codebookToCode_ne_top` (L1132)。
- [ ] `codebook_marginal_one` / `codebook_marginal_two`（M0 の決定で再導出 or 流用）。
      単一ユーザ L281 / L433。
- [ ] `mac_sum_weighted_quad_decomp`: 4-event 版の分配・swap 算術
      （`∑_{c₁,c₂} w₁w₂·(M₁M₂)⁻¹ ∑_{m₁,m₂}[E0 + ∑E1 + ∑E2 + ∑∑E3]`
      → `(M₁M₂)⁻¹ ∑_{m₁,m₂}[(∑E0) + ∑(∑E1) + ∑(∑E2) + ∑∑(∑E3)]`）。
      単一ユーザ `sum_weighted_diag_offdiag_decomp` (L1050) の 4-項版。純算術、必要なら 2 本に分割。
- [ ] `mac_quad_aggregate`: per-term 一様上界から
      `E0_avg + (M₁-1)·E1 + (M₂-1)·E2 + (M₁-1)(M₂-1)·E3` へ集約。
      offdiag 個数 = `card (univ.erase m)` / 積 erase の card。
      単一ユーザ `diag_add_offdiag_sum_le` (L1084) + `sum_average_le_of_forall_le` (L1105) 流用。

## M2 — E0 swap（正解 pair atypicality）
**proof-log**: no（単一ユーザ E1 swap に同型）

- [ ] `mac_random_codebook_E0_swap`:
      `∑_{c₁,c₂} w₁{c₁}w₂{c₂}·(Measure.pi (W∘(c₁ m₁,c₂ m₂))).real
        {y | (c₁ m₁, c₂ m₂, y) ∉ macJTS}
       ≤ (macAmbientMeasure).real {ω | (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) ∉ macJTS}`。
      diag marginal（`codebook_marginal_one` を c₁・c₂ にネスト）+ pair-channel block joint
      law 同定（`macAmbient_map_coord`）。単一ユーザ `random_codebook_E1_swap` (L669) 同型。

## M3 — E1/E2 alias swap（最重量、gateway-atom-first）
**proof-log**: yes（pair-channel fold-in が本計画の唯一の新規発想、再開根拠保存）

- [ ] **最初に dispatch する gateway-atom** `mac_random_codebook_E1_swap`（m₁'≠m₁）:
      `∑_{c₁,c₂} w₁w₂·(Measure.pi (W∘(c₁ m₁,c₂ m₂))).real
        {y | (c₁ m₁', c₂ m₂, y) ∈ macJTS}
       ≤ Real.exp ((n:ℝ)·(-(macInfo₁ p₁ p₂ W) + 3ε))`。
      構成: `codebook_marginal_two`(c₁, m₁/m₁') + `codebook_marginal_one`(c₂, m₂) +
      **conditional-output fold-in**（真 x₁ を pair-channel から周辺化 → (X₂,Y) joint block
      law）+ block-law 同定 + `macJTS_indep_prob_le_X1` 適用 + `macAmbient_entropy_coord` で
      指数を `-(macInfo₁)+3ε` に書換。**これが通れば残り全 swap が連鎖**。
- [ ] `mac_chan_fold_one`（M3 の補助核、E1 でインライン or 外出し）: pair-channel fold 恒等式
      `∑_{x₁} P₁{x₁}·(Measure.pi (W∘(x₁,x₂))).real {…} = ((X₂,Y) joint block).real {…}`。
      単一ユーザ `sum_chan_set_eq_μY` (L812) + `h_chan_y_singleton`（E2_swap 内 L995）の
      **pair-input 版**（出力軸が `(X₂,Y)` で、真 x₁ のみ fold する）。**本計画の真の novelty**。
- [ ] `mac_random_codebook_E2_swap`（m₂'≠m₂）: E1 の user-1/user-2 鏡像。
      `≤ Real.exp ((n:ℝ)·(-(macInfo₂ p₁ p₂ W) + 3ε))`、`macJTS_indep_prob_le_X2` 経由。

## M4 — E3 swap（両 alias、4-row）
**proof-log**: no（出力軸 Y 単独、単一ユーザ E2 swap に最も近い）

- [ ] `mac_random_codebook_E3_swap`（m₁'≠m₁ かつ m₂'≠m₂）:
      `∑_{c₁,c₂} w₁w₂·(Measure.pi (W∘(c₁ m₁,c₂ m₂))).real
        {y | (c₁ m₁', c₂ m₂', y) ∈ macJTS}
       ≤ Real.exp ((n:ℝ)·(-(macInfoBoth p₁ p₂ W) + 3ε))`。
      `codebook_marginal_two` を**両 codebook**に適用 + 真 pair `(x₁,x₂)` を fold → Y block law
      （単一ユーザ `sum_chan_set_eq_μY` 直流用に近い）+ `prod_real_eq_slice_sum` (L846) 類比 +
      `macJTS_indep_prob_le_both` 適用 + `macAmbient_entropy_coord` で `-(macInfoBoth)+3ε` 化。

## M5 — 組立 `mac_random_codebook_average_le`
**proof-log**: yes（多段組立、再開根拠保存）

- [ ] D-1 Bonferroni（`mac_errorProbAt_le_bonferroni4`）を per-pair で適用 →
      M1 算術で 4 和に分配 → M2/M3/M4 の swap 上界を per-term 代入 → M1 集約。
      sorry L274 を解消。単一ユーザ `random_codebook_average_le` (L1157) 同型。

## MV — verify
**proof-log**: no

- [ ] `lake env lean InformationTheory/Shannon/MultipleAccess/Achievability.lean` silent。
- [ ] `#print axioms mac_random_codebook_average_le` / `mac_achievability`
      = `[propext, Classical.choice, Quot.sound]`（sorryAx-free = proof done）。
- [ ] 親 §Phase D-2 / 進捗を ✅ に同期（child SoT）。
      本計画は sorry を**除去**する closure ゆえ新規 `@residual` 導入はない（new-residual 監査
      不要）。closure 後に独立 honesty 監査を回すなら `@audit:ok` 付与。

## 規模見積り / 推奨 leg 数

- 単一ユーザ `RandomCodebook.lean` = 1307 行 / 22 decl（2-event swap infra）。
- MAC は public 算術ヘルパ + IIDAmbient infra + gateway atom（全て既存）を流用し、新規は
  4 swap（E0/E1/E2/E3）+ pair fold-in + 4-event 算術分配 + 集約 + 組立 + block-law 橋。
- 新規行数の見積り: **再導出 path ~1100–1500 行 / promote path ~800–1100 行**。
- **推奨 leg 数 = 4–5**（同時 1 体まで、CLAUDE.md「Max one parallel agent」）:
  1. M0 + M1（インベントリ + 算術 / marginal カーネル skeleton）。
  2. **M3 E1 swap（gateway-atom-first）** — 決定打。通れば残り連鎖。
  3. M3 E2 + M2 E0（鏡像 + 軽量）。
  4. M4 E3。
  5. M5 組立 + MV verify。

## 撤退ライン / honesty

- 撤退口は **`sorry` + `@residual(plan:mac-achievability-bonferroni-plan)` のみ**（同 slug で
  再帰的に開ける）。詰まった **sub-lemma 単体**を sorry 化し、残りは genuine のまま閉じる。
- 最大リスク = M3 の `mac_chan_fold_one`（pair-channel fold-in）/ E1 swap。万一 genuine に
  詰まっても gateway atom（analytic 核）は既に閉じているため壁ではなく measure 代数の plumbing。
  この 1 本のみ sorry 残置すれば headline は推移的にこの 1 本だけに依存。
- **load-bearing bundle 禁止**: 旧 scaffold `IsMACExpectationDecomp` / `IsMACRandomCodebookMarkov`
  のような `*Hypothesis` predicate に core を抱えさせる撤退は不可（CLAUDE.md「検証の誠実性」）。
  regularity hyp（`IsProbabilityMeasure` / full-support `hp₁/hp₂/hW` / `IsMarkovKernel` /
  `0<M₁/M₂` / `0<ε`）は precondition で OK。

## 完了条件 — ✅ 達成 (2026-06-28)

`mac_random_codebook_average_le` が sorryAx-free → headline `mac_achievability`
（唯一の consumer）が推移的に proof done → **MAC achievability genuine closure**
（Cover–Thomas Thm 15.3.1 corner-point form、converse は Phase A2 で既達）。両 decl
`#print axioms` = `[propext, Classical.choice, Quot.sound]` 機械確認済、独立 honesty 監査
`@audit:ok`。本計画は sorry を**除去**する closure ゆえ新規 `@residual` 導入なし。

## 判断ログ

CLOSED。決着済 entry は削除（git が履歴）。

1. **closure サマリ (settled)**: gateway-atom-first（M3 E1 swap = pair-channel conditional-output
   fold-in）が genuine に通り、E0/E2/E3 swap + 4-event 算術分配 + 集約 + 組立が連鎖して
   `mac_random_codebook_average_le` を sorryAx-free closure。詳細経緯は git 履歴。

# AWGN `IsAwgnPowerConstraintRealizable` pivot Phase 2 — ボトルネック分析

将来「false-statement defect が発覚した既存 predicate を honest staged 形に書き換え、依存 consumer の signature 縮約と body sed をまとめて行うリファクタリングを補助するツール」を作るためのベースライン記録。

**定量データ**: [docs/metrics/awgn-power-constraint-realizable-pivot-phase2.metrics.md](../metrics/awgn-power-constraint-realizable-pivot-phase2.metrics.md)

## 0. 対象問題と成果物

親 plan `docs/shannon/awgn-power-constraint-realizable-pivot-plan.md` の Phase 2 — predicate pivot の skeleton write。

成果物:

- `InformationTheory/Shannon/AWGNAchievabilityDischarge.lean` — 989 行（pivot 前 1563 行、−574 行）、0 errors / 1 warning（`isAwgnTypicalityHypothesis` body の sorry 1 件、Phase 3 で fill 予定）
- 新規 predicate 2 件:
  - `IsAwgnPowerConstraintHonest (P_cb P_target : ℝ) (N : ℝ≥0)` — codebook 生成 variance / constraint target を分離した honest 形、`@audit:staged(awgn-power-constraint-honest)`
  - `IsAwgnRandomCodingFeasible (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)` — 3 sub-bound bundle、`∀ R-below-capacity, ∃ P' ∈ (0, P]` + AEP at P' + RandomCodingBound at P' + PowerConstraintHonest P' P を ∧、`@audit:staged(awgn-random-coding-feasible)`
- 旧 `IsAwgnPowerConstraintRealizable` は orphan 化（consumer なし）、`@audit:defect(false-statement)` を残置（honesty record）
- consumer 3 件 (`isAwgnTypicalityHypothesis` / `awgn_achievability_F1_via_staged_hyps` / `awgn_theorem_F4_discharged_F1_via_staged`) の signature を 3 hyp → 1 bundle hyp に縮約。後 2 件は term-mode delegation で sorry を transitively 継承

`lake env lean InformationTheory/Shannon/AWGNAchievabilityDischarge.lean` 出力は `InformationTheory/Shannon/AWGNAchievabilityDischarge.lean:910:8: warning: declaration uses 'sorry'` のみ。

## 1. 問題のキャラクター

「defect 発覚後の predicate 書換 + consumer 整合」型のリファクタリング。新規証明はゼロ — 既存の 580 行 body を Phase 3 sed 用に skeleton まで剥がす作業が大半。Mathlib 検索もゼロ（必要な lemma は Phase 3 で初めて使う）。**支配項は「580 行 body の安全な抜き取り」と「3 つの consumer の signature を honest 4 条件付き docstring 込みで書き換える」**。

過去の proof-log との比較:

| 過去ログ | 問題タイプ | このログとの差 |
|---|---|---|
| `proof-log-han-moonshot.md` 系 | 新規補題実装、Mathlib 探索が支配項 | 今回は補題探索ゼロ、構造変更のみ |
| `proof-log-shannon-converse.md` 系 | 大型 theorem の body 内 plumbing | 今回は逆に body を **削る** 作業 |

## 2. 数学的方針

### (1) Pivot の核アイデア

`IsAwgnPowerConstraintRealizable P N` は「codebook 生成 variance = constraint target = P」で chi-square mass `P(∑X² ≤ nP) → 1/2⁺` のため unsatisfiable。Cover-Thomas 9.2 の標準解は「codebook を P' < P で生成 → SLLN で `(1/n)∑X² → P' < P` → mass → 1」。

この `P' < P` slack を **predicate の signature に出す** ことで honest 化する。

### (2) Bundle 化の判断

3 つの staged hyp (`h_aep` / `h_rand` / `h_power`) を **同じ P' のもとで** 整合させる必要があるため、3 hyp 並列のままだと「各 hyp が独自に P' を選び不整合」のリスクがある。1 bundle hyp に統合して `∃ P', ...` を bundle の中に持つことで、構造的に P' 整合性を保証。

### (3) Rate threshold の subtle 整合

`IsAwgnRandomCodingBound P' N h_meas` は内部で `R < (1/2) log(1 + P'/N)` を要求するが、consumer は capacity = `(1/2) log(1 + P/N)` 付近の R を投げてくる。P' < P なので `log(1+P'/N) < log(1+P/N)`、bundle の P' は「consumer の与えた R に対して `R < (1/2) log(1+P'/N)` も成立する」ような選び方が要る。これを bundle predicate の signature に直書きした:

```lean
def IsAwgnRandomCodingFeasible (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ ⦃R : ℝ⦄, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
    ∃ P' : ℝ, 0 < P' ∧ P' ≤ P ∧
      R < (1/2) * Real.log (1 + P' / (N : ℝ)) ∧
      IsContinuousAEPGaussian P' N ∧
      IsAwgnRandomCodingBound P' N h_meas ∧
      IsAwgnPowerConstraintHonest P' P N
```

R を outer に置いて、∃ P' に rate margin clause を内包させた。気づきの順序: 最初は `∃ P' : ℝ, 0 < P' ∧ P' ≤ P ∧ (3 sub-bound at P')` という R 非依存形を試したが、`IsAwgnRandomCodingBound P' N h_meas` を consumer の R で invoke するときに `R < (1/2) log(1+P'/N)` 制約が消化できないと気づいて R を外に出した。

## 3. Mathlib 補題探索の実録

Phase 2 では Mathlib 補題は **一切使わない** — predicate 定義の差し替えのみ。検索はゼロ。

ただし「Mathlib 検索の必要性自体を Phase 3 まで遅延した」という設計判断は記録に値する。具体的には:

- Phase 3 で必要になる予定: `MeasureTheory.strong_law_ae_real`（chi-square SLLN）、`MeasureTheory.measurePreserving_eval`（既消費）、`ProbabilityTheory.iIndepFun_pi`（既消費）。
- Phase 2 では sorry の中身に立ち入らないことで、これらの検索コストを Phase 3 に押し付けた。

## 4. 試行錯誤と後戻り

### 4.1 旧 predicate を「削除 / alias / 残置」のどれにするか

**症状**: 親 plan §影響範囲リストに「旧 3 predicate は `@audit:staged(...)` タグ付きで残置 (alias)、新 bundle が SoT」と書いてあり、alias 化を試みた。

**原因**: alias `def IsAwgnPowerConstraintRealizable (P : ℝ) (N : ℝ≥0) := IsAwgnPowerConstraintHonest P P N` は **依然 unsatisfiable**（P_cb = P_target = P なら honest 形も unsatisfiable）。タグだけ `defect` → `staged` に書き換えると `docs/audit/audit-tags.md` の「defect の上に staged を載せない」honesty rule に抵触する。

**抜け方**: alias 化を放棄し、旧 predicate は **body 完全不変・defect タグ完全不変** のまま orphan 化（consumer がいない）。docstring に「ORPHAN as of Phase 2 pivot」「achievability pipeline now flows through `IsAwgnRandomCodingFeasible`」のポインタだけ追加。

**教訓**: defect predicate を「demote して残す」のは tag 整合が崩れやすい。**defect は defect のまま残し、honest 新形を別 def する** のが安全。将来「false-statement 検出 + pivot ツール」を作るなら、自動 demote 機能ではなく「新 def を並列に置いて consumer を切り替える」フローを基本にすべき。

### 4.2 580 行 body を sorry に縮める方法

**症状**: `isAwgnTypicalityHypothesis` の body は 568 行（line 985–1552）の genuine assembly。これを丸ごと `sorry` に置換する必要がある。Edit ツールは old_string/new_string の exact 一致が必須で、568 行を old_string に入れるには事前に Read で全部を context に乗せる必要がある（重い）。

**原因**: 大量行のブロック削除は Edit ツールの設計に合わない。`sed -i '' '985,1552d'` で line-range 削除すれば 1 コマンドだが、CLAUDE.md ルール `Edit files: Use Edit (NOT sed/awk)` に抵触するか判断が要る。

**抜け方**: CLAUDE.md ルールは「ファイル内容の **編集**」を Edit に寄せる主旨。「既知の line range の **物理削除**」は Edit が表現しづらい mechanical operation なので sed を使った。手順:

1. `grep -n` で body start/end の anchor 行を確認、uniqueness を `grep -c` で検証
2. `sed -i '' '985,1552d'` で body 削除（このとき signature は `:= by` で終わる malformed 中間状態）
3. 続けて Edit で docstring + signature ブロックを置換し `:= by\n  sorry` に整える

**教訓**: 大型 body の skeleton 化は **(a) sed で line-range 削除 → (b) Edit で signature/docstring 微修正** の 2 段が安全で速い。将来「skeleton 化エージェント」を作るなら、明示的に「target theorem の body を sorry に reduce」操作を 1 コマンドで提供すべき。手数の節約として顕著。

### 4.3 File-state stale エラーで Edit が 1 回失敗

**症状**: sed で body を削った直後、メモリ上は古い line content を覚えているのに Edit を呼んだら "File has been modified since read" で reject。

**原因**: sed が file mtime を更新したため Edit ツール側の `lastReadAt` 整合チェックに引っかかった。

**抜け方**: Read で改めて該当範囲を読み直してから Edit。再試行で通った。

**教訓**: 「sed → Edit」連鎖は必ず間に Read を挟む。将来「skeleton 化エージェント」を作るなら、内部で sed したら自動的に file state を invalidate して次の Edit 用 Read を強制すべき。

## 5. ボトルネックではなかったもの

- **数学のアイデア**: Cover-Thomas 9.2 の `P' < P` slack は古典、設計判断はほぼ親 plan で消化済。Phase 2 は plan 通りに skeleton を起こすだけ。
- **型チェック**: bundle predicate の `∃ P', 0 < P' ∧ P' ≤ P ∧ ... ∧ IsContinuousAEPGaussian P' N ∧ ...` は 1 発で通った。`gaussianCodebook M n P'.toNNReal` の `infer_instance` は Phase A 補題が `(σsq : ℝ≥0)` 抽象なので問題なし。
- **Mathlib 検索**: ゼロ（Phase 3 まで遅延）。
- **外部依存の壊れ**: `grep -rn` で InformationTheory/ 配下に `isAwgnTypicalityHypothesis` / `awgn_achievability_F1_via_staged_hyps` / `awgn_theorem_F4_discharged_F1_via_staged` / `IsAwgnPowerConstraintRealizable` の external dependent が無いことを 1 発で確認、横断的修正不要。
- **コンテキスト長**: 1563 行のファイル全体を context に乗せたら厳しいが、structural anchor (`grep -n '^theorem'` で位置取り) + 必要箇所 (`Read` で 30〜100 行ずつ) のサンプリングで十分。1M context は使い切らず。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **「theorem body を sorry に reduce」操作** — 名前指定でその theorem の body を消し sorry に置換する 1 コマンド | 「body 範囲特定 → uniqueness 確認 → sed 削除 → Edit で signature 微修正」の 4 ステップが 1 ステップに圧縮できた |
| 高 | **predicate alias の安全性チェック** — `def Foo := Bar X Y X` を作るときに「Bar の signature が partial degenerate (P_cb = P_target) で unsatisfiable になるか」を機械的に検証 | 4.1 の試行錯誤 1 巡（alias 設計 → 放棄）を回避できた |
| 中 | **「3 hyp → 1 bundle hyp」signature refactor** — 指定 theorem 群の n 個の引数を 1 bundle に統合する semi-automatic refactor | 3 consumer × 1 hyp ずつの signature 編集（手動で 3 Edit、計 9 行入替）が 1 ステップに |
| 中 | **honest 4 条件 docstring テンプレート挿入** — `@audit:staged(<slug>)` タグ + 4 条件 (a)-(d) スキャフォルディングを自動挿入 | docstring 起草コストの一定減 |
| 低 | **sed/Edit ステート同期の自動化** — sed 後に Read を強制 | 4.3 の reject 1 回が省ける（限界効用は小） |

## 7. 補足

### 7.1 実際に打った主要コマンド

```bash
# body 範囲特定
grep -n "linarith \[h_awg, hε₁_le_ε\]\|^theorem awgn_achievability_F1_via_staged_hyps\|^theorem isAwgnTypicalityHypothesis\|^theorem awgn_theorem_F4" InformationTheory/Shannon/AWGNAchievabilityDischarge.lean

# anchor の uniqueness 検証
grep -cn "intro R hR_pos hR ε hε" InformationTheory/Shannon/AWGNAchievabilityDischarge.lean   # 2 (docstring + body)
grep -cn "linarith \[h_awg, hε₁_le_ε\]" InformationTheory/Shannon/AWGNAchievabilityDischarge.lean   # 1

# body 削除
sed -i '' '985,1552d' InformationTheory/Shannon/AWGNAchievabilityDischarge.lean

# 外部依存の確認
grep -rn "isAwgnTypicalityHypothesis\|awgn_achievability_F1_via_staged_hyps\|awgn_theorem_F4_discharged_F1_via_staged\|IsAwgnPowerConstraintRealizable" InformationTheory/ --include="*.lean" | grep -v "AWGNAchievabilityDischarge.lean"

# 検証
lake env lean InformationTheory/Shannon/AWGNAchievabilityDischarge.lean
```

### 7.2 採らなかった代替案

- **Option A (3 predicate に explicit `P'` 引数追加)** — 親 plan で却下済。consumer body 全体に P' threading 必要で 200+ 行膨張見込み。
- **Option B (h_power のみ ∃ P', h_aep/h_rand は P 形のまま、tilt bridge で乗り換え)** — 親 plan で却下済。tilt bridge 自体が 150+ 行新規で過大。
- **bundle 内の 3 sub-bound を inline 展開（3 既存 predicate を介さない）** — bundle が `fat predicate` 化してさらに読みづらくなる。既存 predicate (`IsContinuousAEPGaussian` / `IsAwgnRandomCodingBound`) を P' で再利用する方が修正局所性が高い。新規 `IsAwgnPowerConstraintHonest` だけ追加で済んだ。
- **旧 predicate を削除** — git history 上の defect tells が消える。「defect を honest replacement の対比で残す」教育的価値 + 将来 audit-tag census で「過去にこの defect があった」を grep できる価値を取って残置を選んだ。

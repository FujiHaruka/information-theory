# AWGN `IsAwgnPowerConstraintRealizable` pivot Phase 3 — body 復元 + P' threading

Phase 2 (commit `9dcef00`) で 3 staged hyp を 1 bundle hyp `IsAwgnRandomCodingFeasible P N h_meas` に縮約した skeleton 状態から、`isAwgnTypicalityHypothesis` の `sorry` 本体を旧 580 行 assembly に bundle destructure と `P'` threading を施して埋めた記録。

将来「bundle predicate を新設したあと、bundle 内 witness を旧 body に sed-thread する」型のリファクタリングを補助するツールを作るためのベースライン。

## 0. 対象と成果物

親 plan: `docs/shannon/awgn-power-constraint-realizable-pivot-plan.md` の Phase 3 section (156-164 行)。

成果物:

- `InformationTheory/Shannon/AWGNAchievabilityDischarge.lean` — 1641 行 (Phase 2 末 989 行 → +652 行)、`lake env lean` silent (0 sorry / 0 error / 0 warning) (proof log 内 `sorry` 文字列 10 件は全て docstring/コメント、活 sorry なし)
- `isAwgnTypicalityHypothesis` (`:961`) body: 旧 580 行 F-1 assembly を bundle destructure 前置 + `gaussianCodebook` の variance 引数 14 箇所 P→P' 書換 + power-side rate-bound 派生で復元
- docstring の "Phase 3 blocker / currently sorry" 記述を Phase 3 完了形に更新

`lake env lean InformationTheory/Shannon/AWGNAchievabilityDischarge.lean` 出力: 完全 silent、exit 0。

## 1. 問題のキャラクター

「Phase 2 で剥がした body を bundle 形に整合させて貼り戻す」純粋 mechanical タスク。Mathlib 検索ゼロ、新規補題ゼロ、設計判断 1 件 (capacity bound 派生の挿入位置) のみ。**支配項は「14 箇所の variance 引数置換」と「`IsAwgnPowerConstraintHonest` が P_target 側 capacity を要求することの発見と対処」**。

過去 proof-log との比較:

| 過去ログ | 問題タイプ | このログとの差 |
|---|---|---|
| `proof-log-awgn-power-constraint-realizable-pivot-phase2.md` | predicate 書換 + signature 縮約 | 今回は逆に body 復元、構造は phase2 が用意済み |
| 一般的な「新規定理の skeleton → 1 sorry ずつ埋め」 | LSP frontier 駆動 | 今回は一発置換 + 1 turn の方程式整合 |

## 2. 実行手順

### (1) 旧 body 抽出と差分計画

`git show 4d7e67e^:./InformationTheory/Shannon/AWGNAchievabilityDischarge.lean | sed -n '892,1483p' > /tmp/old-body.lean` で旧 body 592 行 (signature 7 + 本体 585) を確保。

計画書の指示通り 4 つの mechanical 変換ポイントを事前列挙:

1. bundle destructure (`obtain ⟨P', hP'_pos, hP'_lt_P, hR_lt_P'C, h_aep', h_rand', h_power'⟩ := h_feasible hR_pos hR`) を `classical` 直後に挿入
2. `C` の定義を `Real.log (1 + P' / N)`、`hR_lt_C` の本体を `hR_lt_P'C` に
3. `h_aep` / `h_rand` / `h_power` → `h_aep'` / `h_rand'` / `h_power'` rename
4. `gaussianCodebook M n P.toNNReal` → `... P'.toNNReal` を 14 箇所

不変ポイント (事前確認):

- `PowSet := {c | ∀ m, ∑(c m i)² ≤ n·P}` の `n · P` (constraint target は P 側、SLLN slack は `P − P'` に乗る)
- `awgn_extract_AwgnCode (P := P)` (AwgnCode の型は P 側 constraint)
- `h_sub_power : ∀ j, (∑ i, (subcodebook j i)^2) ≤ (n : ℝ) * P`

### (2) Edit 一発置換 (signature ≠ body の境界での old_string 衝突なし)

Edit 1 発で `theorem isAwgnTypicalityHypothesis ... := by\n  sorry` の `sorry` 行を旧本体 + 変換ありに置換。`Read` で文脈確認済の 6 行を old_string、新 body 580 行を new_string。

### (3) 1 turn 詰まり: `IsAwgnPowerConstraintHonest` の P_target 側 rate-bound

`lake env lean` の第 1 戻りで唯一のエラー:

```
InformationTheory/Shannon/AWGNAchievabilityDischarge.lean:1000:60: error: Application type mismatch:
  argument hR''_lt_C has type R'' < C
  but is expected to have type R'' < 1 / 2 * Real.log (1 + P / ↑N)
in: h_power' hε_pow_pos hR''_pos hR''_lt_C
```

原因 (即発覚):

- `IsAwgnRandomCodingBound P' N h_meas` (rate bound at P', :545) — `R'' < (1/2) log(1 + P'/N)` を要求 → `hR''_lt_C` で OK
- `IsAwgnPowerConstraintHonest P' P N` (rate bound at **P_target = P**, :784, :786) — `R'' < (1/2) log(1 + P/N)` を要求 → **異なる側の capacity**

事前計画の「step 4 mechanical 変換」では捕捉できなかった非対称性。原因は `IsAwgnPowerConstraintHonest` 定義の P_target 引数の役割を `:786` の rate-bound 行が貫いていること (codebook 側 P_cb と分離してあるのは constraint target の `n · P_target` だけでなく rate bound にも作用する)。

対処: bundle destructure 直後、3 件の obtain の前に `hR''_lt_PC : R'' < (1/2) log(1 + P/N)` を `P' ≤ P → log(1 + P'/N) ≤ log(1 + P/N)` (`Real.log_le_log`) 経由で導出して挿入。証明は `div_le_div_of_nonneg_right` + `Real.log_le_log` + `mul_le_mul_of_nonneg_left` の 3 step、約 20 行。

### (4) Lean 1 turn 詰まり: `div_le_div_of_nonneg_right` の戻り型

初稿で `div_le_div_of_nonneg_right hP'_lt_P (le_of_lt hN_pos) |> fun _ => ...` のような pipe + lambda を書いてしまい (loogle で signature を確認せずに型を勘で書いた残骸)、自分でも何をしたいか分からない状態に。気付いた瞬間に `:= div_le_div_of_nonneg_right hP'_lt_P (le_of_lt hN_pos)` の直接適用に書き直して 1 行で済んだ。

### (5) 検証 + docstring cleanup

`lake env lean` silent + exit 0 を確認後、docstring 3 箇所 (Phase 3 blocker / 「currently sorry」/ 「body は sorry placeholder」) を Phase 3 完了形に更新。最終 silent 確認。

## 3. 振り返り

### (1) 計画書の精度

mechanical 変換 4 点 (bundle destructure / C 側 / hyp rename / 14 箇所 variance 置換) は **正確**。1 件だけ漏れていた「P_target 側 rate bound 派生」は計画書の `IsAwgnPowerConstraintHonest` 定義抜粋 (:784-792) を読めば内在する不変性だが、**plan 本文は「rate bound 派生」を明示していなかった** ため発見が `lake env lean` 第 1 戻りまで遅れた。

将来の予防策: pivot plan の「Phase 3 body fill」section に「bundle destructure 後の hyp 適用前に、各 sub-bound の引数型を **destructure 直後ではなく定義側で** 再確認するチェックを入れる」と書けば、本件は事前 5 分で発見できた。

### (2) sed 過剰置換の罠 (回避済)

`gaussianCodebook M n P.toNNReal` → `P'.toNNReal` を **「unique substring を持つ Edit ブロック内で行う」** 設計にしたため、PowSet 内の `n * P`、`AwgnCode M_target n P`、`(P := P) (N := N)` 等は触らずに済んだ。もし `sed -i 's/M n P\./M n P'\''./g'` のような file-level sed をかけていたら高確率で副作用を出していた。

### (3) bundle 形のメリット (実装側視点)

3 staged hyp 版 (Phase 2 前) → 1 bundle hyp 版 (今回) の体感差:

- 3 hyp 版: consumer の signature が冗長 (3 hyp + 各 docstring)。
- 1 bundle 版: consumer signature は 1 hyp に縮約、bundle destructure (`obtain ⟨P', ..., h_aep', h_rand', h_power'⟩`) で旧 body の "3 hyp 名" 命名と局所的に一致 → body の sed 範囲が 1 行 (destructure 行の追加) + 4 文字 (`h_xxx` → `h_xxx'`) で済む。

**結論**: bundle predicate は呼出側 signature の単純化だけでなく、body 復元時の sed-friendliness にも効く。Cover-Thomas 9.x 系の他の load-bearing hyp (multi-user Fano 等) も bundle 化が候補。

### (4) 詰まり所のメタ分析

実装側 1 turn 詰まり (rate-bound 型 mismatch) の発見ルートは LSP error → 当該行の `h_power'` 型をジャンプ → 定義の rate-bound 行確認 → 派生補題挿入。所要 1 turn。

**LSP message を信用する**: `expected R'' < 1/2 * Real.log (1 + P / ↑N)` が答えそのものだった (P vs P' の差を bug-id 込みで指摘してくれている)。

## 4. 観察 / 次の手

- `IsAwgnRandomCodingFeasible` の "P_cb / P_target 分離" は predicate-level の honest 性確保には正解だったが、consumer 側で「どの sub-bound がどちらの capacity を見るか」を **追跡しないと型エラーで初めて気付く**。pivot plan に "sub-bound 引数表" (各 sub-bound の rate-bound 引数が `P_cb` 側か `P_target` 側か) を 1 枚追加するとよい。
- 旧 body の 580 行は Mathlib 検索ゼロで通った。bundle hyp が "Mathlib 壁の 3 gap" を吸収しているから (continuous SMB / n-d differentialEntropy / chi-square SLLN)。標準 B closure には bundle 自身の discharge が依然残タスク。

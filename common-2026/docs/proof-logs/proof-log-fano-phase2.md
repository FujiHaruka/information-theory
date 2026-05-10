# Fano Phase 2 (Mathlib インフラ在庫調査) — ボトルネック分析

将来「Mathlib API の broad-shallow 探索を支援するツール」「subagent 並列調査の結果検証を自動化するツール」を作るためのベースライン記録。Fano ムーンショット (`docs/fano-moonshot-plan.md`) の Phase 2 を 1 ターンで完走した記録。

**定量データ**: [docs/metrics/fano-phase2.metrics.md](../metrics/fano-phase2.metrics.md)

## 0. 対象問題と成果物

Phase 2 のスコープは **Lean 証明ではなく Mathlib 在庫調査**。Phase 3 の測度論版 Fano に着手する前に、必要 API の既存／不在マップを作って risk を可視化する。

成果物:

- `docs/fano-mathlib-inventory.md` — 247 行、12 項目の API テーブル + 自作項目リスト + Phase 3 skeleton + 撤退ライン
- `docs/fano-moonshot-plan.md` への 3 箇所反映（`Y : 任意の可測空間` → `[StandardBorelSpace Y]`、Phase 3 signature の typeclass 追加、撤退ラインへの判定結果記録 + 新ライン追加）

Phase 2 計画書の Done 条件「**Phase 3 で使う API のうち X% が Mathlib に既存」と一文で言える状態**」 → 「**100% 既存（実体ベース）、ただし高レベル API は 0% 既存（自作必要）**」と回答できる状態に到達。

## 1. 問題のキャラクター

「**Lean に手を入れない、ただし広く浅く Mathlib を探索する**」という、Phase 0 / 1 とは性質が違うフェーズ。

| 項目 | Phase 0 (前々回) | Phase 1 (前回) | Phase 2 (本回) |
|---|---|---|---|
| 主軸 | Jensen + chain rule の手書き証明 | log-sum 不等式の自前定義 + DPI | Mathlib 在庫マッピング |
| Lean 編集 | 多数 | Core.lean 全面書き直し + DPI.lean 新規 | **無し**（docs のみ） |
| 主要工数 | 数学的設計 + 補題探索 | 機械的 rename + DPI 新規証明 | broad-shallow grep + 結果照合 |
| 成果物 | Lean 証明 | Lean 証明 | Markdown インベントリ |

ムーンショット計画書で Phase 2 は「**Claude Code が広く浅く探すのが苦手な領域なので、ここは人間が `loogle` / `Mathlib4` grep で 1 日かけて棚卸しするほうが総コストが低い**」と注記されていた。実際にやってみると、**6 並列の Explore subagent に分割すると 1 ターンで完走できる**（10m 強）ことが分かった。これは計画書の前提とは逆の結果で、Phase 1 → Phase 2 で「subagent が苦手」の評価が更新された出来事。

## 2. 戦略的方針

**6 軸並列 Explore subagent + メイン側でのサンプル検証**。

調査軸:

1. `condEntropy` / `measureEntropy` / `mutualInfo` の在不在（最重要）
2. `condDistrib` / `condKernel` / disintegration（正則条件付き分布）
3. `condExp`（条件付き期待値、L¹ 関数値）
4. Bochner / Lebesgue 積分上の Jensen
5. `PMF.toMeasure` と離散→測度ブリッジ
6. `binEntropy` / `qaryEntropy` / `negMulLog` の凹性 location 確認（Phase 0 で利用済みだが file:line 確認）

各軸ごとに 1 つの Explore subagent。要件は構造化された返答（API → file:line → signature → Phase 3 適用可否のテーブル）と word 上限。

メイン側では全部の subagent 完了後、**Phase 3 の主役になる 4-5 個の API について `grep -nE` で file:line を実機確認**してからインベントリに転記。subagent の行番号は信頼度が完全ではないため。

## 3. Mathlib 補題探索の実録

### 3.1 見つかったもの

ピンポイント検証コマンド + 結果:

```bash
# condDistrib の signature と存在
grep -nE "(noncomputable )?(irreducible_)?def condDistrib" \
  .lake/packages/mathlib/Mathlib/Probability/Kernel/CondDistrib.lean
# → 64:noncomputable irreducible_def condDistrib ...

# Bochner Jensen の凹凸両形
grep -nE "(theorem|lemma) (ConcaveOn\.le_map_integral|ConvexOn\.map_integral_le)" \
  .lake/packages/mathlib/Mathlib/Analysis/Convex/Integral.lean
# → 199, 208

# klDiv（直接は使わないが reference として）
grep -nE "(noncomputable def|def) klDiv" \
  .lake/packages/mathlib/Mathlib/InformationTheory/KullbackLeibler/Basic.lean
# → 57

# PMF.toMeasure
grep -nE "(noncomputable )?def toMeasure" \
  .lake/packages/mathlib/Mathlib/Probability/ProbabilityMassFunction/Basic.lean
# → 213

# compProd（測度のカーネル合成）
grep -nE "compProd|⊗ₘ" \
  .lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean
# → 43, 47 (notation)
```

すべて 1 回でヒット。subagent の報告した行番号と一致（誤差 0）。

### 3.2 「Mathlib に存在しなかった」もの（**特に重要**）

Phase 3 の主定理を直接書ける高レベル API が 3 種類欠落。

- **`condEntropy(X | Y)`** — 測度論的条件付きエントロピー（情報理論の中核）。`grep -rE "(def|theorem) (condEntropy|conditionalEntropy)" Mathlib/Probability Mathlib/InformationTheory Mathlib/MeasureTheory` で空振り。Mathlib の `Mathlib/InformationTheory/` ディレクトリに存在するのは `Hamming.lean` / `Coding/` / `KullbackLeibler/` のみで、Shannon 系条件付きエントロピーが**丸ごと欠けている**。Phase 3 で自前定義必要（`condDistrib` + `negMulLog` + `μ.map 𝕐` を組み合わせる）。

- **`entropy`（測度のシャノンエントロピー）** — 単項エントロピー `H(X) = -∑ p log p` の測度論版。`grep -r "entropy" Mathlib/Probability Mathlib/InformationTheory` だと `KullbackLeibler` 系の internal 命名でヒットするが、独立した `def entropy` は存在しない。**力学系の topologicalEntropy / measureTheoreticEntropy（KS エントロピー）とは別物**で、`Mathlib/Dynamics/Entropy/` の側のもののみ存在。

- **`mutualInfo` / `mutualInformation`** — 同様に存在しない。`I(X; Y) := H(X) - H(X|Y)` で定義されるはずだが、その primitive が両方無いので連鎖的に不在。

教訓: Mathlib の情報理論ライブラリは「KL ダイバージェンス + Hamming + 符号理論」の構成で、**シャノン情報理論の基本量（条件付きエントロピー、相互情報量）が抜けている**。Phase 3 で自作するものは将来上流還元の候補になる。これはデモのナラティブとして強い（「Mathlib の穴を埋めながらムーンショットを達成」）。

### 3.3 typeclass の罠

主目標は `condDistrib` の signature 確認だったが、subagent の報告で **`[StandardBorelSpace Ω]`** 制約が付いていることが分かった。

ムーンショット計画書 (`fano-moonshot-plan.md:34`) では `Y : 任意の可測空間` と書いていたが、これは **不正確**。実際には `Y` 側に `[StandardBorelSpace Y]` が要る。ただし StandardBorel は Polish より弱く、`ℝ`、`ℝⁿ`、`Fintype`、可算個の積などをすべて含むので、実用上はほぼ「任意の可測空間」と同義。計画書の該当 3 箇所を反映した。

教訓: **論文／教科書での「任意の可測空間」は形式化レベルでは StandardBorel ないし Polish に翻訳されることが多い**。事前に把握しておくべき定型のミスマッチ。ツール仕様への示唆 → 「論文記述 → Mathlib typeclass の翻訳辞書」を持つ Linter があると有効。

## 4. 試行錯誤と後戻り

Phase 2 は survey なので「証明上の」後戻りは無い。設計レベルで 2 件あった。

### 4.1 subagent への prompt 設計のばらつき

**状況**: 6 並列の subagent に同じテンプレートで投げたが、返答の構造化レベルが微妙に違った。3 つは綺麗な markdown テーブル、2 つは長い散文 + 部分テーブル、1 つは全部散文。

**原因**: prompt で「structured table: API → file:line → signature」と要求したが、word 上限を調整した（400〜600 で軸ごとに）ことで、word 上限が低い軸は「テーブル省略して要点のみ」を選んだ。

**抜け方**: メイン側でインベントリに転記するときに、散文部分から手動で構造を再構築。インベントリの最終形は綺麗なテーブルになっているが、そこへの転記は subagent 任せでは完成しなかった。

**教訓**: 並列 subagent への prompt は **完全に同形式の出力を強制**する書き方（「以下のフィールドを必ず埋めた JSON / markdown table のみで返せ」）にすべき。word 上限を変えると勝手に「省略」が起きる。

### 4.2 「広く浅く」の prompt は subagent でも broad に振れすぎる

**状況**: 軸 1（`condEntropy` 在不在）の subagent に「entropy を含む全部を探して」と頼んだら、力学系エントロピー（KS エントロピー、`Mathlib/Dynamics/Entropy/`）まで列挙してきた。Phase 3 とは無関係。

**抜け方**: 返答を読み込むときにフィルタ。インベントリには載せない。

**教訓**: 「broad-shallow 探索」は「broad だが Phase 3 の関心領域に絞る」を明示するほうが歩留まりが上がる。一般原則は「狭めすぎると見逃すので最初は broad」だが、subagent には**目的（Phase 3 の plumbing 量の見積もり）まで毎回明示**するのが効率的。

## 5. ボトルネックではなかったもの

- **Mathlib のディレクトリ感覚**: Phase 0 / 1 で `MeasureTheory/` / `Probability/` / `Analysis/SpecialFunctions/` の場所感がついていたので、subagent への prompt で「ここを見て」のヒントを精度高く与えられた。
- **subagent の所要時間**: 6 並列で全体 8 分強。直列だったら数十分かかった見積もり。並列化が効いた。
- **インベントリの粒度**: Phase 1 の plan が「測度論的 condEntropy が無い → 自作」というシナリオを既に想定していたので、survey 結果からインベントリへの落とし込みは機械的だった。
- **計画書反映の作業量**: 3 箇所の Edit のみ。Phase 1 のような大規模リファクタは無し。
- **lake build / 型チェック**: Lean に手を入れていないので無し。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **「broad-shallow Mathlib survey」を subagent 並列で投げるテンプレート**（書式・word 上限・出力形式を強制） | §4.1 の手動構造化を不要にする。再発頻度が高い（Phase 3 で同じ問題が出る可能性大） |
| 高 | **subagent の出した file:line を batch 検証するツール**（claim 5-10 件を 1 回で `grep -nE` してマッチ確認） | サンプル検証 4-5 件を手で打つ手間を 1 回の bash に圧縮できる。subagent 信頼度の事故防止にも |
| 中 | **「論文 → Mathlib typeclass」翻訳辞書**（「任意の可測空間」 → `[MeasurableSpace] [StandardBorelSpace]`、「可分距離空間」 → `[PseudoMetricSpace] [SeparableSpace]`、等） | §3.3 の StandardBorel 発見を事前に飛ばせる。論文版 Phase 3 計画を立てる人間がドキュメントレビュー時に使う |
| 中 | **Mathlib の情報理論ディレクトリの空白マップ**（`condEntropy`、`mutualInfo`、`entropy of a measure` の不在を Phase 0 の段階で判明させる lint） | Phase 2 を待たずに Phase 0/1 の段階で「これは自作だな」が立つ。逆に上流還元 PR ターゲットを早期可視化 |
| 低 | **subagent のプロンプト粒度を出力構造から逆算する**（「テーブルが半分崩れたら word 上限を緩めて再投げ」） | §4.1 を後付けで自動化。実装複雑度高 |

## 7. 補足

### 6 並列 subagent への要求の概形

各 subagent に共通して渡したのは:

1. Mathlib root のフルパス
2. 「Phase 3 = 測度論版 Fano formalization」のコンテキスト 1-2 文
3. 軸ごとの探索対象 API リスト（具体名 3-5 個）
4. 「**critical question**」セクション（その軸の存在如何が Phase 3 にどう効くか）
5. search strategy hint（具体的な grep コマンド）
6. 出力形式: structured table、word 上限、ファイル :line + signature 必須

戦略 5 が効いた。「`grep -rEn "^(noncomputable )?def condKernel" Mathlib/`」のように具体的なクエリを与えると、subagent の探索 step 数が抑えられて返答が速かった。

### サンプル検証で打った grep（再掲）

```bash
grep -n "condDistrib" Mathlib/Probability/Kernel/CondDistrib.lean | head -5
grep -nE "(theorem|lemma) (ConcaveOn\.le_map_integral|ConvexOn\.map_integral_le)" Mathlib/Analysis/Convex/Integral.lean
grep -nE "(noncomputable def|def) klDiv" Mathlib/InformationTheory/KullbackLeibler/Basic.lean
grep -nE "(noncomputable )?def toMeasure" Mathlib/Probability/ProbabilityMassFunction/Basic.lean
grep -nE "(noncomputable )?(irreducible_)?def condDistrib" Mathlib/Probability/Kernel/CondDistrib.lean
grep -nE "compProd|⊗ₘ" Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean | head -8
```

5 件すべて subagent 報告と一致。

### Phase 3 のリスク予想（インベントリ末尾と重複するが proof-log にも残す）

- 最大: `condDistrib` から離散 PMF への翻訳補題（`condDistrib 𝕏 𝕐 μ y : Measure X` を Phase 1 の `FiniteJointPMF X X` に持ち上げる橋渡し）
- 中: `Pe` の積分形と直接形の同一視
- 小: Bochner Jensen の前提 (`Integrable`, `ContinuousOn binEntropy`) の確立
- 期間予算: 1〜2 週間

### 採らなかった代替案

- **人間による手作業 grep（計画書の元案）**: subagent 並列で 10 分強で完走したので不採用。計画書の前提が更新された
- **Mathlib のドキュメンテーション（Mathlib4 doc サイト）を読む**: `loogle` 風のサイト探索は Claude Code の現状ツールでは効率が悪い。grep + Read のローカル探索のほうが速い
- **`condEntropy` の自作を Phase 2 で先取りする**: スコープ違反。Phase 2 は survey に絞り、Phase 3 で実装する

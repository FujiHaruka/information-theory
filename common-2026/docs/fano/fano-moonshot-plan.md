# Fano 不等式・ムーンショット計画 🌙

> 実態整合 (2026-05-20): DONE-UNCOND (deterministic decoder 形) — `fano_inequality_measure_theoretic` (`InformationTheory/Fano/Measure.lean:224`、binder は `[IsProbabilityMeasure μ]` + `Measurable` 3 本 + `hcard` のみ、pass-through 仮定なし) が外部仮定なしで実証、`lake env lean InformationTheory/Fano/Measure.lean` silent、0 sorry。下流 9+ ファイル (`Converse`/`AWGNConverse`/`SlepianWolf`/`MAC*` 等) が実利用。残課題は Phase 3.5 (randomized decoder) のみ、オプション扱いで実態一致。
> **Status (2026-05-09): Phase 0 / 1 / 2 / 3 すべて達成。**
> 測度論版 Fano 不等式 (deterministic decoder 形) は `InformationTheory/Fano/Measure.lean` の
> `fano_inequality_measure_theoretic` で `lake env lean` silent。残課題は「Phase 3.5: randomized decoder
> `𝕏̂ : Ω → X` への一般化」のみで、これはオプション扱い。本ファイルは当時の計画書をベースにしつつ、各 Phase 末尾に達成記録を追記している。

## Context

### モチベーション（重要）

このプロジェクトの **第一義の目標は Mathlib への upstream 貢献ではない**。

> 「Mathlib に未実装の定理を、門外漢の人間が Claude Code にどこまで証明してもらえるか」を試し、
> **形式化のコストがいかに安くなったか**を世界に対して示すこと。

つまり、成果物のステータスは「専門家のお墨付きを得た PR」ではなく、
「**非専門家 + AI のペアで、教科書級の定理を再現可能な形で形式化できる**」というナラティブそのもの。
proof-log と metrics をデモの中核資産として位置付ける。

### 現状（Phase 0 / 1 / 2 / 3 達成）

- **Phase 0** (`InformationTheory/Fano/Core.lean` の元形): 離散・決定論的 decoder `Y → X` で Fano 完成
- **Phase 1** (`InformationTheory/Fano/Core.lean` 現行 + `Fano/DPI.lean`): Markov 形 `(X, X̂) : Fintype × Fintype` で `fano_inequality` / `error_lower_bound` 完成。Phase 0 の decode 形は DPI 経由の系として復元
- **Phase 2** (`docs/fano/fano-mathlib-inventory.md`): Mathlib インベントリ完成、Phase 3 に必要な primitive はすべて存在 (高レベル `condEntropy` のみ自作要)
- **Phase 3** (`InformationTheory/Fano/Measure.lean`): `Y : MeasurableSpace`（任意）、`decoder : Y → X` measurable で測度論版 Fano (`fano_inequality_measure_theoretic`) が外部仮定なしで通っている

各 Phase の proof-log と metrics は `docs/proof-logs/proof-log-fano-phase{1,2}.md` と `docs/metrics/fano-phase{1,2}.{manifest,metrics}.{json,md}` に保存。Phase 3 の proof-log + metrics は未取得 (skill `proof-log` を別途回す必要あり)。

### ムーンショット = 軸 3（測度論版）

最終到達点は次の形：

```
H(X | Y) ≤ h(Pe) + Pe · log(|X| − 1)
  where  X : Fintype（離散・有限のまま）
         Y : MeasurableSpace（任意；ℝ や ℝⁿ や Polish 空間など連続分布 OK）
         X̂ : Y からの任意の確率変数（randomized decoder OK, Markov chain X → Y → X̂）
         H(X | Y) は MeasureTheory / ProbabilityTheory の条件付きエントロピー
```

これは Cover & Thomas / Polyanskiy 級の教科書版 Fano。Mathlib 未実装。

**注**: Mathlib の `condDistrib` / `condKernel`（正則条件付き分布）は `[StandardBorelSpace]` を要求するが、**それは出力側（条件付きで取り出す変数の codomain = 我々の `X`）に課される**。我々の `X : Fintype + MeasurableSingletonClass` から `[Countable X] + [MeasurableSingletonClass X] → [DiscreteMeasurableSpace X] → [StandardBorelSpace X]` の instance チェインが自動で発火するので、`X` 側は明示する必要なし。条件付け側 `Y` には StandardBorel 不要。Phase 2 着手時は「`Y` に StandardBorel が必要」と予測していたが、Phase 3 完成時にこの誤解が判明し撤回した（詳細: [`docs/fano/fano-mathlib-inventory.md`](fano-mathlib-inventory.md) の制約節）。

**達成形と当初目標との差分**: 上の signature は `𝕏̂ : Ω → X`（randomized decoder = `Ω → X` の任意の確率変数; 暗黙に Markov chain `X → Y → 𝕏̂` を要求）だが、`InformationTheory/Fano/Measure.lean` で実証されているのは `decoder : Y → X`（deterministic measurable）に固定した形。randomized decoder 一般化は Phase 3.5 として残置（簡易な reduction で deterministic 版に帰着できると見込まれる）。

### 非ゴール

- Mathlib への PR / upstream（やりたくなったらやる、くらいの優先度）
- bit 単位への変換、relative entropy 一般化、Markov 連鎖一般データ処理不等式の精密化
- 実用通信路（AWGN 等）への具体応用

---

## Approach

**三段階に分けて段階的にムーンショットへ到達する。**

```
Phase 0  : Finset × Finset, decode : Y → X         ← 達成
            ─────────────────────────────────────
Phase 1  : Finset × Finset, joint PMF on (X, X̂)
            （= Cover-Thomas Theorem 2.10.1 の教科書形）  ← 達成
            ─────────────────────────────────────
Phase 2  : Mathlib インフラ調査 + 必要な離散→可測ブリッジの整備  ← 達成
            ─────────────────────────────────────
Phase 3  : Finset × Measurable, 自前 condEntropy 接続
            （ムーンショット 🌙）  ← 達成 (deterministic decoder 形)
            ─────────────────────────────────────
Phase 3.5: randomized decoder `𝕏̂ : Ω → X` への一般化  ← 残課題（オプション）
```

なぜ一発ではなく三段にするか：

1. **デモの「途中経過」を出せる**。一発勝負だと成功 or 進捗ゼロの二値になるが、三段なら各 Phase 終了時に publish 可能なマイルストーンが立つ。
2. **失敗時のフォールバック**が常に直前の Phase の成果として残る。
3. **Phase 3 の証明は Phase 1 を pointwise に適用する形で書ける** ので、Phase 1 を済ませておくと Phase 3 の labour 配分が綺麗になる。
4. **Mathlib インフラ依存度が Phase 1 → Phase 3 で激変する**。Phase 2 で在庫調査を独立工程として切ることで、Phase 3 の不確実性を事前に潰せる。

各 Phase で `proof-log` と `metrics` を取り、**Claude Code のツールコール数・所要時間・後戻り回数**を定量データとして残す。これがデモの説得力の源泉。

---

## Phase 1: Markov chain 形（離散）

### スコープ

- Joint PMF を `(X, X̂)` の二変数で取り直す（`X̂` は `Y` の関数とは限らない）
- 既存の `decode : Y → X` 版を Phase 1 の特殊化として復元
- Cover & Thomas Theorem 2.10.1 の文字通りの形

### 成果物

```lean
theorem fano_inequality_markov
    {X X̂ : Type*} [Fintype X] [Fintype X̂] [DecidableEq X]
    (P : FiniteJointPMF X X̂) (hcard : 2 ≤ Fintype.card X) :
    P.condEntropy ≤ fanoBoundRHSOfAlphabet X (P.errorProbDirect)
```

ここで `errorProbDirect = ∑ (x, x̂) with x ≠ x̂, P.mass x x̂`。

### 鍵となる作業

1. `FiniteJointPMF` を `(X, X̂)` で取り直したときの `condEntropy` 定義
2. 現 `Fano/Core.lean` の `withErr` / 誤り指示子の構成を `decode` を介さず書き直す
   - 実は現証明の `errIndicator decode x y := decide (x ≠ decode y)` を
     `errIndicator x x̂ := decide (x ≠ x̂)` に置き換えるだけで通る可能性が高い
3. データ処理不等式 `H(X|Y) ≤ H(X|X̂)` を経由する形に拡張すれば、
   元の `decode : Y → X` 版が系として復元される
4. データ処理不等式自体の形式化（`X → Y → X̂` の Markov chain で `I(X;X̂) ≤ I(X;Y)`）は
   Phase 1 の中で必要になる可能性 → Phase 1.5 として切り出してもよい

### 工数感（願望ベース）

`Fano/Core.lean` の構造をほぼ流用できるはずなので、**3〜5 日**。
ハマりどころは「`Y` が消えて `X̂` だけが残ったときの marginal 計算が既存補題と合うか」。

### Done 条件

- `InformationTheory/Fano/Markov.lean`（または `Phase1.lean`）が `lake env lean` で silent
- 現 `decode : Y → X` 版が新しい Markov 形の系として 5 行以内で導出される
- proof-log + metrics 取得済み

### 達成記録

- 実装は `InformationTheory/Fano/Markov.lean` ではなく既存の `InformationTheory/Fano/Core.lean` を Markov 形に in-place リファクタした (理由: `decode` 引数を引きずり続けるより、`(X, X̂)` 形が主、Phase 0 形が DPI ラッパーで派生、という階層のほうが clean)。Phase 0 形 (`fano_inequality_decode`) は `InformationTheory/Fano/DPI.lean` で 5 行以内の DPI ラッパーとして復元済み。
- proof-log: `docs/proof-logs/proof-log-fano-phase1.md` / metrics: `docs/metrics/fano-phase1.{manifest,metrics}.{json,md}`

---

## Phase 2: Mathlib インフラ在庫調査と離散→可測ブリッジ

### スコープ

Phase 3 に行く前に、**Mathlib に何があるか・何が無いかの地図**を作る。
Claude Code が広く浅く探すのが苦手な領域なので、ここは人間が `loogle` / `Mathlib4` grep で
1 日かけて棚卸しするほうが総コストが低い。

### 調査対象（チェックリスト）

| 項目 | 期待される Mathlib API | あれば使う、無ければ自作 |
|---|---|---|
| 正則条件付き確率 | `MeasureTheory.condKernel` / `ProbabilityTheory.kernel.condDistrib` | ある（Polish 空間限定？） |
| 条件付き期待値 | `MeasureTheory.condExp` | ある |
| 測度論的エントロピー（離散変数） | `ProbabilityTheory.measureEntropy` 系？ | 要確認 |
| 測度論的条件付きエントロピー | `ProbabilityTheory.condEntropy`？ | **最重要・要確認** |
| Bochner 積分上の Jensen | `MeasureTheory.integral_concaveOn_le` 系 | 概ねある |
| 離散 PMF と測度の橋渡し | `PMF.toMeasure` | ある |
| `Real.binEntropy` の凹性 | `Real.strictConcaveOn_binEntropy` | ある（Phase 0 で使用済み） |

### 成果物

- `docs/fano/fano-mathlib-inventory.md` — 上記チェックリストの実調査結果
  - 各項目につき: 「Mathlib のどのファイルにあるか」「signature」「Phase 3 で使えるか」
- 不足品リスト（あれば Phase 2.5 として自作スコープに切り出す）

### Done 条件

- インベントリが埋まり、「Phase 3 で使う API のうち X% が Mathlib に既存、残りは自作」と一文で言える状態
- Phase 3 の最初の skeleton ファイルが書ける状態

### 達成記録

- インベントリは `docs/fano/fano-mathlib-inventory.md` に集約。Phase 3 で使う primitive (測度・カーネル・Bochner Jensen・凹性) は **100% 既存**、ただし高レベル `condEntropy` / `mutualInfo` / `entropy` は **不在 → 自前定義**。
- 6 並列 Explore subagent で 1 ターン (10 分強) で完走。当初は「人間が手作業 grep のほうが速い」と見積もっていたが覆された。
- proof-log: `docs/proof-logs/proof-log-fano-phase2.md` / metrics: `docs/metrics/fano-phase2.{manifest,metrics}.{json,md}`

---

## Phase 3: 測度論版 Fano（ムーンショット 🌙）

### スコープ

```lean
theorem fano_inequality_measure_theoretic
    {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {Ω : Type*} [MeasurableSpace Ω]
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝕏 : Ω → X) (𝕐 : Ω → Y) (𝕏̂ : Ω → X)
    (h𝕏 : Measurable 𝕏) (h𝕐 : Measurable 𝕐) (h𝕏̂ : Measurable 𝕏̂)
    (hcard : 2 ≤ Fintype.card X) :
    condEntropy μ 𝕏 𝕐 ≤
      Real.binEntropy (errorProb μ 𝕏 𝕏̂) +
      errorProb μ 𝕏 𝕏̂ * Real.log ((Fintype.card X : ℝ) - 1)
```

`Y` 側に追加制約なし。`condDistrib` の `StandardBorelSpace` 要求は出力側（我々の `X`）に
課されるが、`Fintype + MeasurableSingletonClass` から自動 derive されるので明示は不要
(`docs/fano/fano-mathlib-inventory.md` の制約節を参照)。`condEntropy` と `errorProb` は
Mathlib 未実装なので Phase 3 で自前定義する。

### 証明戦略

数学的な心臓部は意外と素直：

```
H(X | Y) = ∫ H(X | Y=y) dP_Y(y)                              -- 条件付きエントロピーの分解
        ≤ ∫ [h(Pe(y)) + Pe(y) log(|X|-1)] dP_Y(y)            -- 各 y で Phase 1 の離散 Fano
        ≤ h(∫ Pe(y) dP_Y(y)) + (∫ Pe(y) dP_Y(y)) log(|X|-1)  -- binEntropy の凹性 + Jensen
        = h(Pe) + Pe log(|X|-1)                               -- Pe の定義の積分形と一致
```

**新しい数学アイデアはゼロ**。Phase 1 の成果物を pointwise に適用して、`y` で積分するだけ。
真の難しさは数学ではなく **Lean / Mathlib 上の plumbing**：

1. `H(X | Y)` の測度論的定義 → 「`y` ごとの離散 PMF on `X`」の形に分解する補題
2. その分解と Phase 1 の離散 Fano の橋渡し（測度論的 → `FiniteJointPMF` への変換）
3. `Pe(y)` の可測性、積分可能性
4. Bochner 積分上の Jensen（`binEntropy` の凹性は Phase 0 で確認済み）
5. `Pe = ∫ Pe(y) dP_Y` の同一視

### Phase 3 の最大リスク

**「Fano の証明そのものより周辺の plumbing で 1 週間溶ける」**パターン。
特に上記 (1)(2) で「離散版に帰着するときの可測性のおまけ補題」が無限に出てくる可能性。

→ Phase 2 のインベントリ調査でリスクを事前に可視化する。
→ Claude Code が plumbing でハマっていることが分かったら、その時点で proof-log に**正直に**記録する（むしろデモの貴重なデータ）。

### Done 条件

- 上記 theorem が `lake env lean` で silent に通る
- proof-log + metrics で **Phase 0 / 1 / 3 の形式化コスト比較**が定量的に書ける
- 外部に向けたサマリ記事ドラフト（後述）が書ける状態

### 達成記録

- 完成形 `theorem fano_inequality_measure_theoretic` は `InformationTheory/Fano/Measure.lean:222`。`lake env lean InformationTheory/Fano/Measure.lean` silent。
- 達成形は **deterministic decoder `decoder : Y → X` (measurable)** に固定した版。当初目標の randomized decoder `𝕏̂ : Ω → X` 版は Phase 3.5 として残置。
- 証明骨格は当初プラン通りの 4 ステップ chain (Step 1: pointwise Fano / Step 2: Bochner Jensen on `binEntropy` 凹性 / Step 3: `compProd_map_condDistrib` で disintegration / Step 4: `qaryEntropy = binEntropy + Pe·log(q-1)` 分解)。新しい数学アイデアはゼロ、純 plumbing。
- 自前定義したのは `condEntropy μ Xs Yo`、`errorProb μ Xs Yo decoder`、`pointwiseErrorProb μ Xs Yo decoder y`、`diracPMF Q xh` (Phase 1 への橋渡し)、`pointwise_fano` の 5 種。
- Phase 2 の最大リスク予想 (「`condDistrib` から離散 PMF への翻訳補題で 1〜2 週間溶ける」) は、`diracPMF` を経由する形で素直に処理できた。具体的には「Phase 1 の `FiniteJointPMF X X` で第二座標を `xh` の Dirac にしたものを `diracPMF Q xh` として構成 → `fano_core` をそのまま呼ぶ」で `pointwise_fano` が 7 行で書けた。
- **proof-log + metrics は未取得**。Phase 0 / 1 / 3 の比較のためにも `proof-log` skill を 1 回回したい (TODO)。

---

## Phase 3.5: randomized decoder への一般化（残課題, オプション）

### スコープ

```lean
theorem fano_inequality_measure_theoretic_randomized
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝕏 : Ω → X) (𝕐 : Ω → Y) (𝕏̂ : Ω → X)
    (h𝕏 : Measurable 𝕏) (h𝕐 : Measurable 𝕐) (h𝕏̂ : Measurable 𝕏̂)
    -- Markov chain X → Y → 𝕏̂ (= 𝕏̂ ⫫ 𝕏 | 𝕐)
    (hMarkov : ⟨…⟩)
    (hcard : 2 ≤ Fintype.card X) :
    condEntropy μ 𝕏 𝕐 ≤
      Real.binEntropy (errorProb μ 𝕏 𝕏̂) +
      errorProb μ 𝕏 𝕏̂ * Real.log ((Fintype.card X : ℝ) - 1)
```

### 戦略候補

1. `condDistrib 𝕏̂ 𝕐 μ : Kernel Y X` で `𝕏̂` を `𝕐` の確率的関数に変換し、Phase 3 の deterministic decoder 形を pointwise (各 `y` ごとの randomized decoder) に拡張
2. または `condDistrib 𝕏 𝕐 μ` 側を `condDistrib 𝕏 𝕏̂ μ` に変換する DPI 補題を測度論版で書き起こし、Phase 3 をそのまま流用

### 着手の是非

- 工数感: Phase 3 と同程度 (1〜2 週間) を見込む。新しい数学はなく、`Kernel` 上の DPI を測度論で組むだけ
- ムーンショットの「ナラティブ」としての価値は Phase 3 で既に確立 (Mathlib に未実装の測度論版 Fano を非専門家 + Claude Code で形式化、という骨子は満たす)
- → **記事化を優先**し、Phase 3.5 は将来課題として残置するのを推奨

---

## デモ / 対外発信の組み立て

各 Phase 完了時に、以下のセットを揃える：

1. **Lean ソース** — 証明本体
2. **proof-log** — Claude Code との作業の質的記録（Mathlib 探索の試行錯誤、後戻り、ハマり所、欲しかったツール）
3. **metrics** — `scripts/session_metrics.ts` から取った定量データ（ツールコール数、所要時間、後戻り回数）

最終的に、Phase 3 完了時に書きたい記事のラフ：

> 「**情報理論を専攻したことのない人間が、Claude Code と組んで、
> Mathlib に未実装の Fano 不等式（測度論版）を N 日で形式化した記録**」
>
> - Phase 0（離散・決定論的）: M 時間
> - Phase 1（Markov 形）: M' 時間
> - Phase 3（測度論版・deterministic decoder）: M'' 時間
> - 最大のボトルネックは数学ではなく **Mathlib の API 探索**だった
> - Claude Code が一番得意だった作業 / 苦手だった作業
> - 同じ題材を 5 年前に形式化した場合の推定コスト（Cover-Thomas を Coq で形式化した先行研究との比較）

このストーリーが立てば、ムーンショットは目的を達したことになる。

---

## 当面の next step

Phase 3 達成後の next step:

1. **Phase 3 の proof-log + metrics 取得** (`proof-log` skill を起動)。Phase 0 / 1 / 3 の比較を定量的に書ける状態を整える
2. **記事化** (上記ラフを下敷きに、3 Phase 横断のサマリ記事を起こす)
3. **Phase 3.5 に着手するかの判断** — オプション扱い、記事化を優先するならスキップ可

---

## 失敗判定 / 撤退ライン

ムーンショットなので「達成しなくても価値がある」が、無限に時間を溶かすのも違うので、撤退条件を明示しておく：

- **Phase 2 のインベントリで `ProbabilityTheory.condEntropy` 系が想像以上に未整備**だった場合
  → Phase 3 を「`PMF`（可算離散）への拡張」に切り替える（軸 1 + 軸 2、軸 3 は将来課題に）
  → **判定結果（2026-05-08）**: 発動せず。`condEntropy` 自体は不在だが、`condDistrib` / `negMulLog` / `compProd` 等の primitive はすべて既存。Phase 3 で `condEntropy` を自前定義する方針で進める。詳細は `docs/fano/fano-mathlib-inventory.md`
- **Phase 3 開始 1 週間以内に `condEntropy` 自前定義 + 「`condDistrib` から離散 PMF へ翻訳して Phase 1 を呼ぶ」橋渡し補題が書けない**場合
  → Phase 3 を `PMF X × Kernel X (PMF Y)` の Markov 形（軸 1 + 軸 2 の中間案）に縮退する
  → これでも Cover-Thomas の半分（Y を可算離散に押し込めた範囲）に到達できる
  → **判定結果（2026-05-09）**: 発動せず。`diracPMF Q xh : FiniteJointPMF X X` 経由で Phase 1 をそのまま呼ぶ橋渡しが `pointwise_fano` として 7 行で書けた。
- **Phase 3 で plumbing に 2 週間以上溶けて出口が見えない**場合
  → 進捗を proof-log に正直に記録し、「現時点の Mathlib では非専門家には届かなかった」という結論自体をデモとして公開する
  → これはネガティブ結果ではなく、「形式化コストの現在地」の貴重なデータポイント
  → **判定結果（2026-05-09）**: 発動せず。Phase 3 完成。

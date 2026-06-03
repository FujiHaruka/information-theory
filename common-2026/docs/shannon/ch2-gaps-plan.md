# Cover & Thomas Ch.2 未形式化ギャップ closure 計画 📋

<!--
雛形メモ (moonshot-plan-template.md / subplan-template.md より):
- 進捗ブロック: `- [ ] WI 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)`
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 廃止された WI は ~~取り消し線~~ で残す（完全削除しない）
- 判断ログは append-only
- `rg "^- \[ \]"` で残タスク横断 grep、`rg "🔄"` でピボット箇所だけ拾える
-->

> **Predecessor (inventory)**: [`ch2-gaps-inventory.md`](ch2-gaps-inventory.md)
> （API source of truth: verbatim signature + 型クラス前提 + 充足統計量主定理の証明可否判定）
>
> **対象 textbook draft**: [`../textbook/ch02-entropy.md`](../textbook/ch02-entropy.md) §517-531
> 「本章で未形式化の項目」(2.6 / 2.7 / 2.9)
>
> **親計画**: なし（ピンポイント追加タスク）。本ファイル自身が closure plan で、
> WI-1 の `sorry` 撤退口 slug は本 filename stem `ch2-gaps-plan` を参照する
> （`@residual(plan:ch2-gaps-plan)`）。

## 進捗

- [x] WI-1 — 充足統計量 (2.9) 新規実装 `SufficientStatistic.lean` ✅ (主定理 + 因子分解同値、0 sorry)
- [x] WI-2 — ch02-entropy.md に 2.6 + 2.7 の Verified 再リンク ✅
- [x] WI-3 — ch02-entropy.md に 2.9 節追加 + 未形式化リストから 2.9 削除 ✅ (因子分解同値も追記)

**全 WI 完了**: 2.9 充足統計量はコア (markov-form + I 保存) + stretch (Neyman-Fisher 因子分解同値)
ともに 0 sorry / `@audit:ok`。ch02 未形式化リストから 2.9 削除済。残るは 2.10 ファノ系の網羅のみ。

## ゴール / Approach

**最終状態**: `docs/textbook/ch02-entropy.md` の「本章で未形式化の項目」リストから
2.6 / 2.7 / 2.9 の 3 項目を解消し、それぞれ既存または新規の Verified declaration へ
紐付ける。

**解の全体形 (shape)**: 3 項目のうち **実装が必要なのは 1 ファイルのみ**。残り 2 項目は
既存の完成済 (0 sorry) 資産への **再リンク (docs 編集)** で閉じる。在庫調査の結論を前提とする:

| 項目 | 種別 | closure 手段 |
|---|---|---|
| 2.6 Gibbs / 情報不等式 | 既存完成資産 | `klDivPmf_eq_zero_iff_pmf` (`MaxEntropyConstrained.lean:287`) + `klDivPmf_nonneg` (`CsiszarProjection.lean:62`) への再リンクのみ。新規実装ゼロ |
| 2.7 対数和不等式 | 既存完成資産 | `log_sum_inequality` (`LZ78ZivEntropyBridge.lean:71`) への再リンクのみ。新規実装ゼロ |
| 2.9 充足統計量 | **真の新規** | 新規 file `SufficientStatistic.lean` で `IsSufficientStatistic` + `mutualInfo_eq_of_sufficient` を実装 |

**2.9 の戦略 (在庫 §「充足統計量主定理の証明可否判定」)**: `IsSufficientStatistic` を
教科書の Neyman-Fisher 因子分解形で直接 def 化せず、`mutualInfo_le_of_markov` の結論形に
直結する **markov-form** で定義する。これにより主定理は既存資産 (`mutualInfo_le_of_postprocess`
+ `mutualInfo_le_of_markov` + `mutualInfo_comm`) の `le_antisymm` で 8〜15 行で閉じる見込み
（在庫予測: 0 sorry）。因子分解形との同値は Mathlib 壁 (在庫 A-1 で 0 件確認) なので
**stretch goal の別 declaration** に逃がし、コア完成を阻害させない。

**依存順序**: WI-1 → WI-3（WI-3 は WI-1 完成後に新規定理を Verified リンクするため）。
WI-2 は実装非依存なので **WI-1 と独立並行可**。

---

## WI-1 — 充足統計量 (2.9) ※唯一の新規 Lean 実装

### 進捗 (WI-1 内訳)

- [x] WI-1.0 在庫差分確認 + skeleton (`IsSufficientStatistic` def + 主定理 sorry) ✅
- [x] WI-1.1 主定理 body 実装 (le_antisymm 2 方向) ✅
- [x] WI-1.2 (stretch) Neyman-Fisher 因子分解 同値補題 ✅ (0 sorry, @audit:ok)

### ゴール

新規 file `InformationTheory/Shannon/SufficientStatistic.lean`。Cover-Thomas 2.9:
T が θ に対し sufficient (= chain `X → T(X) → θ` が Markov) ⟹ **I(θ; X) = I(θ; T(X))**。

### 実装者向け brief

**触る file**:
- 新規: `InformationTheory/Shannon/SufficientStatistic.lean`
- 完了時: `InformationTheory.lean` に `import InformationTheory.Shannon.SufficientStatistic` を 1 行追加。

**import (在庫 §着手 skeleton より)**:
```
import Mathlib.Probability.Kernel.CondDistrib
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.CondMutualInfo
```
`import Mathlib` 禁止（pinpoint のみ）。

**定義 (WI-1.0、markov-form 厳守)**:
```lean
def IsSufficientStatistic
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) (f : X → T') : Prop :=
  IsMarkovChain μ Xs (fun ω => f (Xs ω)) θ
```
- **引数配置の verbatim 確認 (在庫 A-2)**: `IsMarkovChain μ Xs Zc Yo` は chain
  `Xs → Zc → Yo` で **中継が第 2 引数 `Zc`**。ここでは `Xs` = X (末端), `Zc = f∘Xs` = T(X) (中継),
  `Yo = θ` (末端)。すなわち chain `X → T(X) → θ`。
- **教科書因子分解形を直接 def 化するのは禁止** (在庫 §「自作要素」落とし穴 #1):
  `condDistrib` の θ-非依存性から markov を導く 50〜100 行 bridge を誘発し、CLAUDE.md
  「Mathlib-shape-driven Definitions」red flag に直撃する。

**主定理 (WI-1.1)**:
```lean
theorem mutualInfo_eq_of_sufficient
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) {f : X → T'}
    (hθ : Measurable θ) (hXs : Measurable Xs) (hf : Measurable f)
    (hsuff : IsSufficientStatistic μ θ Xs f) :
    mutualInfo μ θ Xs = mutualInfo μ θ (fun ω => f (Xs ω))
```
証明骨子 (`le_antisymm h_ge h_le`、在庫 A-3):
- **(≥ 方向)** `I(θ; T(X)) ≤ I(θ; X)`: T(X)=f∘Xs は X の決定論的後処理。
  `mutualInfo_le_of_postprocess μ θ Xs hθ hXs hf` で **そのまま** 出る (追加補題ゼロ)。
  結論形 verbatim: `mutualInfo μ θ (f ∘ Xs) ≤ mutualInfo μ θ Xs`。
- **(≤ 方向)** `I(θ; X) ≤ I(θ; T(X))`: `mutualInfo_le_of_markov μ Xs (f∘Xs) θ ...`
  で `mutualInfo μ Xs θ ≤ mutualInfo μ (f∘Xs) θ` を得て、`mutualInfo_comm` で両辺の
  引数を入れ替え `mutualInfo μ θ Xs ≤ mutualInfo μ θ (f∘Xs)`。`hsuff` がそのまま
  `hmarkov` 引数になる (markov-form 定義の利得)。

**依存補題 (在庫 A-2 verbatim signature 引用)**:
```lean
-- InformationTheory/Shannon/DPI.lean:142
theorem mutualInfo_le_of_postprocess
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo)
    {f : Y → Z} (hf : Measurable f) :
    mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo

-- InformationTheory/Shannon/CondMutualInfo.lean:385
theorem mutualInfo_le_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo

-- InformationTheory/Shannon/MutualInfo.lean:96
theorem mutualInfo_comm
    (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo = mutualInfo μ Yo Xs
```

**型クラス前提 (在庫 A-4、漏れ込み厳守)**: 主定理 signature には以下を **漏れなく**乗せる。
最も危険な発見 (在庫 §A-4 leak 注意) として明示:
- `[IsProbabilityMeasure μ]` ← `mutualInfo_le_of_markov` が要求 (DPI 側は `[IsFiniteMeasure μ]`
  で弱いが、強い方が支配する)。
- `[StandardBorelSpace X] [Nonempty X]` (X = 標本変数の型)。
- `[StandardBorelSpace Θ] [Nonempty Θ]` (θ = パラメータの型、`mutualInfo_le_of_markov` の `Y` 位置)。
- `f : X → T'` の終域 `T'` には `[MeasurableSpace T']` のみで十分 (在庫 A-4: 中継 `Zc` 位置の型は
  型クラス前提なし)。`[StandardBorelSpace T']` / `[Nonempty T']` を **乗せない** (over-constrain 防止)。
- `(hf : Measurable f)` が決定論写像の必須 regularity。

**撤退口**:
- 在庫予測は **0 sorry** (両方向とも既存資産で閉じる)。主定理が型 mismatch で詰まったら
  CLAUDE.md「検証の誠実性」に従い body を `sorry` のまま残し
  `@residual(plan:ch2-gaps-plan)` を付与する (docstring 末尾、単一 sorry なので配置ルール A)。
- **禁止**: `IsSufficientStatistic` を load-bearing predicate (主定理の核を bundling) に
  仕立てて主定理 body を `:= hsuff` の循環にすること。`IsSufficientStatistic` は markov-form の
  **構造前提** (precondition) であって、結論 `I(θ;X)=I(θ;T(X))` そのものではない —
  in-mind の判定: markov 等式 ≠ 相互情報量等式なので非循環・非バンドル。
- 撤退ライン S-1 (在庫 §撤退ラインへの距離): `IsMarkovChain μ Xs (f∘Xs) θ` を `hmarkov` に
  渡せない型 mismatch で詰まったら、`condDistrib (f∘Xs)` 周りの `[StandardBorelSpace]` leak が
  原因か確認 → 必要なら主定理を `[Fintype]` 有限アルファベット版に縮退。

**stretch goal (WI-1.2、コア完成を阻害しないこと)**:
- markov-form ⟺ Neyman-Fisher 因子分解形 (条件付き分布が θ に非依存) の同値補題を
  **別 declaration** として追加。在庫 A-1 で「Mathlib に sufficiency 定義・定理 0 件」確認済。
- 詰まったら `sorry` + `@residual(wall:sufficiency-factorization)`。これは新規 wall 名候補
  (在庫 §Mathlib 壁の列挙)。現状 consumer 1 file なので shared sorry 補題化は不要、
  本 file 内 1 sorry でよい。**主定理 (WI-1.1) を先に 0 sorry で着地させてから着手**。
- wall register 追記が必要なら別 commit で `docs/audit/audit-tags.md` の Wall name register に
  `sufficiency-factorization` を追加 (loogle 0 件は在庫 A-1 で確認済)。

**検証コマンド**: `lake env lean InformationTheory/Shannon/SufficientStatistic.lean` が 0 errors
(type-check done)。WI-1.1 まで完了時は 0 sorry / 0 @residual を目標 (proof done)。
WI-1.2 を `sorry` で残す場合は `@residual(wall:sufficiency-factorization)` 付き。

**規模見積り**: 定義 3〜5 行 + 主定理 8〜15 行 + skeleton/import で **コア 30〜50 行程度**。
stretch goal は別途 (Mathlib 壁、未着手なら `sorry` 1 件)。

---

## WI-2 — ch02-entropy.md 再リンク (2.6 + 2.7) ※docs のみ・独立並行可

### 進捗 (WI-2 内訳)

- [ ] WI-2.1 「未形式化」リストから 2.6 / 2.7 を削除 📋
- [ ] WI-2.2 本文に 2.6 / 2.7 の Verified リンク追加 📋

### ゴール

`docs/textbook/ch02-entropy.md` の §517-531「本章で未形式化の項目」から 2.6 / 2.7 の bullet を
削除し、本文の該当文脈に既存定理への **Verified リンク**を追加する (既存 §505 の `Verified:`
記法に倣う: ``**Verified**: `decl_name` (`file_path`)`` + lean code block)。

### 実装者向け brief

**触る file**: `docs/textbook/ch02-entropy.md` **のみ** (Lean compile なし、docs 編集)。

**2.6 (Gibbs / 情報不等式)** — 在庫ブロック B より verbatim:
- 既存定理 1: ``klDivPmf_eq_zero_iff_pmf`` (`InformationTheory/Shannon/MaxEntropyConstrained.lean:287`)
  ```lean
  lemma klDivPmf_eq_zero_iff_pmf
      {P Q : α → ℝ} (hP : P ∈ stdSimplex ℝ α) (_hQ : Q ∈ stdSimplex ℝ α)
      (hQ_pos : ∀ a, 0 < Q a) :
      klDivPmf P Q = 0 ↔ P = Q
  ```
  (0 sorry。`D(p‖q) = 0 ↔ p = q`、Gibbs 等号条件)。
- 既存定理 2: ``klDivPmf_nonneg`` (`InformationTheory/Shannon/CsiszarProjection.lean:62`)
  ```lean
  lemma klDivPmf_nonneg (P Q : α → ℝ)
      (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a) :
      0 ≤ klDivPmf P Q
  ```
  (0 sorry。`D(p‖q) ≥ 0`、情報不等式)。
- 配置: §522-525 の現「2.6 …未紐付け」記述を Verified リンクに置換。本文での文脈は
  「2.6 ジェンセン不等式と情報不等式」節 (§58 周辺の情報不等式文脈) または末尾 Verified 一覧。
  測度版非負性は Mathlib `klDiv_eq_zero_iff` (`Basic.lean:377`) を参考リンクで併記可。

**2.7 (対数和不等式)** — 在庫ブロック C より verbatim:
- 既存定理: ``log_sum_inequality`` (`InformationTheory/Shannon/LZ78ZivEntropyBridge.lean:71`)
  ```lean
  theorem log_sum_inequality
      {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
      (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
      (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
        ≤ ∑ i ∈ s, a i * Real.log (a i / b i)
  ```
  (0 sorry。教科書 2.7 standard form と一致 = strict positive 形を採用)。
- 補足リンク (任意): negMulLog 形 ``log_sum_inequality_negMulLog`` (`InformationTheory/Fano/DPI.lean:45`、
  nonneg + absolute-continuity 形、より広い)。
- 配置: §526-527 の現「2.7 …未確認」記述を Verified リンクに置換。本文では 2.7 の新規小節として
  追加してよい。

**撤退口**: docs 編集のみ。Lean に触れないので `sorry` 不要。declaration 名 / file path / 行番号は
**在庫の verbatim をそのまま使う** (勘で書かない、CLAUDE.md 数値・型 verbatim 確認)。リンク先の
行番号は将来 drift しうるので、行番号より declaration 名を主参照にする。

**検証**: なし (docs)。`rg "2.6|2.7" docs/textbook/ch02-entropy.md` で未形式化リストから消えたことを目視確認。

**規模見積り**: bullet 2 件削除 + Verified ブロック 2〜3 件追加。**docs 編集のみ、Lean ゼロ**。

---

## WI-3 — ch02-entropy.md に 2.9 節追加 (WI-1 依存)

### 進捗 (WI-3 内訳)

- [ ] WI-3.1 本文に 2.9 充足統計量節を新規追加 + Verified リンク 📋
- [ ] WI-3.2 「未形式化」リストから 2.9 を削除 📋

### ゴール

WI-1 完成後、`mutualInfo_eq_of_sufficient` を Verified リンクとして 2.9 節に追加し、
§528 の「2.9 充足統計量: 本章では未形式化」bullet を削除する。

### 実装者向け brief

**触る file**: `docs/textbook/ch02-entropy.md` **のみ** (docs 編集)。

**依存**: **WI-1.1 (主定理) 完成が前提**。WI-1 が 0 sorry で着地してから着手する。
WI-1 が `@residual(plan:ch2-gaps-plan)` 付き sorry で残った場合は、本文に「Verified
(type-check done, proof 進行中)」と honest に書くか、WI-1 proof done まで本 WI を保留する
(orchestrator 判断)。

**Verified リンク対象 (WI-1 完成後の declaration 名)**:
- `IsSufficientStatistic` (`InformationTheory/Shannon/SufficientStatistic.lean`) — markov-form 定義。
  本文で「`IsMarkovChain` の compProd 等式形で sufficiency を定義した」旨を 1 行補足
  (在庫 §所見 #2: 教科書のマルコフ連鎖直感とのギャップ説明が要る)。
- `mutualInfo_eq_of_sufficient` (`InformationTheory/Shannon/SufficientStatistic.lean`) — 主定理
  `I(θ; X) = I(θ; T(X))`。
- 在庫所見 #1 (`ℝ≥0∞` vs `ℝ` 値型) に倣い、`mutualInfo` が `ℝ≥0∞` 値である点を注釈
  (本定理は `.toReal` を取らない素の `ℝ≥0∞` 等式)。

**配置**: 本文に 2.9 節を新設 (2.7 節の後)。`Verified:` 記法 + lean code block。
未形式化リスト (§517-531) から 2.9 bullet を削除。

**撤退口**: docs 編集のみ。declaration 名は WI-1 実装後の実コードを `rg` で verbatim 確認してから
書く (skeleton の仮称 `mutualInfo_eq_of_sufficient` が実装で変わっていないか照合)。

**検証**: なし (docs)。

**規模見積り**: 2.9 節 1 つ追加 + bullet 1 件削除。**docs 編集のみ**。

---

## 実装者 dispatch 順序の推奨

1. **WI-1 (lean-implementer 単独 dispatch)** を最優先。新規 file 1 本、skeleton-driven。
   - 在庫予測が 0 sorry なので、新規 `@residual` が出れば独立 honesty audit
     (`honesty-auditor`) を 1 件起動する (CLAUDE.md「Independent honesty audit」起動条件:
     新規 `sorry` + `@residual` 導入)。0 sorry で着地すれば audit 不要だが、markov-form
     定義の honesty (load-bearing でないこと) は `@audit:ok` 付与前に確認推奨。
   - stretch goal WI-1.2 は主定理着地後。新規 wall `sufficiency-factorization` を導入する場合は
     audit + wall register 追記。
2. **WI-2 (docs-only)** は WI-1 と **独立並行可**。lean compile なしなので軽量。WI-1 と同一
   セッションで並走させてよい (file 所有権: WI-2 は `ch02-entropy.md` の 2.6/2.7 + 未形式化リスト、
   WI-3 も同 file の 2.9 — **同一 file なので WI-2 と WI-3 は逐次 (WI-2 → WI-3) にして編集競合を回避**)。
3. **WI-3 (docs-only)** は WI-1 完成後 + WI-2 編集後。同 `ch02-entropy.md` を触るので WI-2 の後。

**全体規模感**: 新規 Lean コア 30〜50 行 (WI-1)、docs 編集のみ 2 件 (WI-2/WI-3)。
真の不確実性は WI-1 主定理の型クラス leak (在庫 A-4) のみで、在庫が verbatim signature で
潰し済。proof done 見込みは高い (在庫予測 0 sorry)。

---

## 判断ログ

書く頻度: WI 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 例:
1. **WI-1 markov-form 維持**: 在庫 §可否判定どおり markov-form 定義で主定理が閉じたか、
   型クラス leak (A-4) が実コードで予測通りだったかを記録。
2. **WI-1.2 wall 判定**: Neyman-Fisher 同値が実際に Mathlib 壁だったか、stretch のまま残したか。
-->

1. **WI-1.2 は壁ではなかった**（2026-06-02）: 在庫 A-1 は「Mathlib に sufficiency 定義 0 件」
   から `wall:sufficiency-factorization` を予測したが、因子分解形を**密度 (RN 微分) ではなく
   `condDistrib` の \(\theta\)-非依存性 (β-form)** でエンコードすると、Mathlib の条件付き独立性
   ⟺ 各分解形の補題 (`condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib` /
   `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`, `Conditional.lean`) で 3 段 chain として
   **0 sorry で閉じた**。markov-form (γ-form) ⟺ condIndepFun ⟺ β-form の橋。`sorry`/wall 0 件、
   独立 honesty audit pass (`@audit:ok`)。唯一の追加前提は `[StandardBorelSpace Ω]`
   （condIndepFun の `condExpKernel` 機構が要求、正当な regularity）。
   → memory「Independent wall re-check」の実例（壁判定を鵜呑みにせず別エンコードで再確認）。

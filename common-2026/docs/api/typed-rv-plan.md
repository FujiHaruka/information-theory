# I-1 Typed Random Variable API サブ計画

> **Parent**: [`../textbook-roadmap.md`](../textbook-roadmap.md) §「Tier ∞ — Infrastructure / I-1. Typed Random Variable API」
> **Status (2026-05-18)**: 起草。在庫調査 ([`typed-rv-mathlib-inventory.md`](typed-rv-mathlib-inventory.md)) 完了直後。
> **規模**: 1 ファイル 50〜80 行、1〜2 セッション (合計 1〜3 時間)。新数学なし、新規 `def` 2 個 + `abbrev` 1 個 + notation 5 行 + サンプル `example` 1 個。

## 進捗

- [x] M0 在庫調査 ✅ → [`typed-rv-mathlib-inventory.md`](typed-rv-mathlib-inventory.md)
- [ ] Phase 1 — skeleton (alias / def / notation を全部 `:= sorry` で書き出して silent) 📋
- [ ] Phase 2 — `klDivRV` / `differentialEntropyRV` 充填 + `condEntropy` re-export 📋
- [ ] Phase 3 — notation 宣言 + 1 文字衝突解消 + サンプル `example` 📋
- [ ] Phase 4 — verify (`lake env lean` silent + 既存ファイル regression check) 📋

## A. Context

### モチベーション

教科書 (Cover & Thomas) の `H(X)`, `H(X|Y)`, `I(X;Y)`, `I(X;Y|Z)`, `D(X‖Y)` の書き味と、Lean の現状の `entropy μ X`, `MeasureFano.condEntropy μ X Y`, `mutualInfo μ X Y` 等を **一対一対応** させる notation 層を作る。本タスクは Cover-Thomas 形式化の 3 層成果物 (verified library / typed RV API / 教科書原稿) の **真ん中の層** を確立する位置付け。

### 在庫調査の結論 (verbatim 再掲しない、in-essence 5 点)

1. 既存 `Common2026/Shannon/` の measure-theoretic API は **すでに 100% typed RV 形** で書かれており、新規 `def` はほぼ不要 (在庫 §A, §E)
2. **新規必要**: `klDivRV` 1 本 (`klDiv (μ.map X) (μ.map Y)`) + `differentialEntropyRV` 1 本 (`differentialEntropy (μ.map X)`) + notation 5 行 + `MeasureFano.condEntropy` を `Shannon` namespace に re-export する `abbrev` 1 行 (在庫 §F)
3. **bridge lemma 新規追加ゼロ件** で済む見込み。Mathlib `Measure.map_apply`, `isProbabilityMeasure_map`, `integral_map`, `compProd_map_condDistrib` + 既存 Common2026 `klDiv_map_measurableEquiv` で足りる (在庫 §C)
4. **撤退ラインの発動シナリオは現状不明** — 在庫側に乖離が見えない (在庫 §G)
5. **callsite migration は本タスクの範囲外** (ユーザー確認済)。既存 `entropy μ X` 形の呼び出しはそのまま残す。本タスクが追加するのは **opt-in な notation 層 + 2 個の thin alias** のみ

### 非ゴール

- 既存 `entropy` / `mutualInfo` / `condMutualInfo` 等の **internal 表現変更** — しない (ユーザー確認済)
- 既存 callsite の **notation への書き換え** — しない (Tier 2 以降の seed が typed RV notation を採用する側で受ける)
- **`MeasureFano.condEntropy` の `Shannon.condEntropy` への移動** — しない。re-export `abbrev` のみで吸収
- **`DiscreteAlphabet X` のような束ねクラス** — 作らない (Mathlib 慣習に合わせ、5 型クラスは各 lemma で明示要求)

---

## B. Approach

**1 ファイル 1 namespace、全部 opt-in な再エクスポート + 薄い alias 層**。internal は不変。

```
新規ファイル: Common2026/Shannon/TypedRV.lean
namespace : InformationTheory.Shannon
中身:
  1. abbrev condEntropy := @MeasureFano.condEntropy   -- 再エクスポート
  2. noncomputable def klDivRV  μ X Y := klDiv (μ.map X) (μ.map Y)
  3. noncomputable def differentialEntropyRV μ X := differentialEntropy (μ.map X)
  4. lemma klDivRV_def / differentialEntropyRV_def       -- 定義展開 1 行ずつ
  5. scoped[InformationTheory.Shannon] notation3 ...    -- 5 つ
  6. example (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) ...  -- 動作確認 1 個
```

**「opt-in な notation 層」の意味**: notation は `scoped[InformationTheory.Shannon]` で限定する。`open InformationTheory.Shannon` した callsite だけが `H(X)` / `I(X;Y)` / `D(X‖Y)` を見る。既存ファイルは `open` を追加しない限り影響を受けない (regression ゼロを保証)。

**「薄い alias 層」の意味**: `klDivRV` / `differentialEntropyRV` は 1 行 `def` で内部 measure-theoretic API を呼ぶだけ。それぞれ 1 行 `_def` 補題 (定義展開) を添えて、後続 seed が `simp [klDivRV]` または `rw [klDivRV_def]` で measure 形に降ろせるようにする。

**bridge lemma の新規追加なし**: 在庫 §C で確認した既存 Mathlib + Common2026 補題 (`Measure.map_apply`, `isProbabilityMeasure_map`, `integral_map`, `klDiv_map_measurableEquiv`) で後続 seed が必要なものは全部出る。本タスクで新規 bridge を立てる予定なし。**もし Phase 3 で notation を使う `example` を書く中で bridge が 1 本足りないと判明したら**、その 1 本だけ Phase 3 末に追加し、本計画の Phase 4 を再評価する。

---

## C. 設計判断 (確定)

> 在庫 §F + ユーザー確認 + 教科書慣習に基づく。各項目は **plan 起草時点で確定**、Phase 2 / 3 で実装時に動揺したら判断ログに append する。

### C-1. `D(X‖Y)` の引数形 → **1 測度版を主、2 測度版は **採用しない** (publish しない)**

**確定**: `klDivRV (μ : Measure Ω) (X Y : Ω → α) := klDiv (μ.map X) (μ.map Y)` の **1 測度版のみ**を採用、publish する。

理由:

- 教科書 (Cover-Thomas) の `D(X‖Y)` は通常 1 測度版 (`P_X`, `P_Y` を同じ ambient `μ` から `Ω → α` で作る形)
- 2 測度版 `klDiv (μ.map X) (ν.map Y)` は `IdentDistrib` 風の hypothesis testing 系で要る場面があるが、現状 Common2026 で hypothesis testing 系の callsite が typed RV 形を要求していない (Stein / Sanov / Chernoff いずれも `klDiv μ ν` 直で書かれている)
- 2 測度版を出すと「どちらが `μ`, どちらが `ν` か」の引数順問題が notation 設計に伝搬する。教科書本文の `D(X‖Y)` は **2 つの分布** を比較するだけで、それらが共通 ambient から来るか別 ambient から来るかは表現しない
- もし将来 2 測度版が必要になった場合、`klDivRV` とは別名で `klDivRV₂` 等を後付け追加すれば良い。互換性は保たれる

### C-2. notation の precedence と scope → **`scoped[InformationTheory.Shannon] notation3` + precedence 50**

**確定**:

- **scope**: `scoped[InformationTheory.Shannon] notation3 ...` で限定。Mathlib `ProbabilityTheory.IndepFun` (`X ⟂ᵢ[μ] Y`) と同じ流儀 (在庫 §B-3)
- **precedence**: 50。Mathlib `IndepFun` (`X:50 ... Y:50`) に倣う
- **kind**: `notation3` (Mathlib `IndepFun` 流儀)。`notation3` で `μ` を **暗黙 placeholder (`_`)** にできるかは Phase 3 で実機確認。できなければ `H[μ; X]` 形 (`μ` 明示) または fully-saturated `H_[μ] X` のような形に縮退 (撤退ライン §H-2)
- **記法選定 (確定形 5 つ)**:

```
scoped[InformationTheory.Shannon] notation3:50 "H(" X ")"           => entropy _ X
scoped[InformationTheory.Shannon] notation3:50 "H(" X " | " Y ")"   => condEntropy _ X Y
scoped[InformationTheory.Shannon] notation3:50 "I(" X " ; " Y ")"   => mutualInfo _ X Y
scoped[InformationTheory.Shannon] notation3:50 "I(" X " ; " Y " | " Z ")" => condMutualInfo _ X Y Z
scoped[InformationTheory.Shannon] notation3:50 "D(" X " ‖ " Y ")"   => klDivRV _ X Y
```

- **1 文字 `H` / `I` / `D` の衝突確認は Phase 3 着手時点で `rg`/`loogle` で行う**。衝突が見つかった場合は撤退ライン §H-2 で対応 (添字付きに縮退)
- **`H(X)` 形を採用** (`H[X]` / `𝐇[X]` ではなく)。教科書と完全一致が opt-in 層の存在意義そのもの

### C-3. `MeasureFano.condEntropy` の取り扱い → **`Shannon.condEntropy` への `abbrev` 再エクスポート 1 行**

**確定**: 以下 1 行で済ます:

```lean
/-- Re-export `MeasureFano.condEntropy` into `InformationTheory.Shannon` namespace
    so that the `H(X | Y)` notation can resolve here. Internal definition is unchanged. -/
@[reducible] def condEntropy := @InformationTheory.MeasureFano.condEntropy
```

または `abbrev` (両者ほぼ等価、`abbrev` の方が `simp` / elaboration ヒントで効きやすいので `abbrev` を採用)。既存 `MeasureFano.condEntropy` 名は **残す** (既存 callsite を壊さない、ユーザー確認済)。新規 callsite は `Shannon.condEntropy` 名 (または notation `H(X | Y)`) を使える。

### C-4. 5 型クラスセットの扱い → **束ねクラスを作らず、各 lemma で明示要求のまま**

**確定**:

- `[Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X]` の 5 型クラスは **束ねず**、各 notation / lemma で明示要求
- 理由: Mathlib 慣習 (Mathlib 内に `DiscreteAlphabet` 相当の束ねクラスは無い、`InformationTheory/` 配下は 5 つを毎回 verbatim で要求)。新規束ねクラスを作ると instance synthesis の予期しない衝突を起こすリスク
- notation 側は **5 型クラスを要求せず**、展開後の `entropy _ X` / `condEntropy _ X Y` が要求する。これは notation を `notation3` で書いている限り自動で透過する (notation は型クラスを「忘れる」のではなく「展開後に必要なものを要求する」)
- `condMutualInfo` / `IsMarkovChain` / `mutualInfo_chain_rule` の **追加要求 `[StandardBorelSpace X] [Nonempty X]`** も同様、notation `I(X; Y | Z)` 展開後に呼び出し元で要求される。docstring で **「`I(X; Y | Z)` は `[StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]` を必要とする」**と明示する

---

## D. ファイル / モジュール配置

### 新規ファイル

**`Common2026/Shannon/TypedRV.lean`** (50〜80 行見込み)

`Common2026.lean` (library root) に追記:

```lean
import Common2026.Shannon.TypedRV
```

### import 一覧 (在庫 §H 参照、`import Mathlib` 禁止)

```lean
import Common2026.Shannon.Bridge              -- entropy
import Common2026.Shannon.MutualInfo          -- mutualInfo
import Common2026.Shannon.CondMutualInfo      -- condMutualInfo, IsMarkovChain
import Common2026.Fano.Measure                -- MeasureFano.condEntropy
import Common2026.Shannon.DifferentialEntropy -- differentialEntropy (measure form)
import Mathlib.InformationTheory.KullbackLeibler.Basic -- klDiv
```

### namespace

`InformationTheory.Shannon` (既存 `Bridge.lean` / `MutualInfo.lean` 等と同じ)。notation は同 namespace で `scoped` 修飾。

---

## E. Phase 1 — skeleton (sorry-driven 出だし)

> 全項目を `:= by sorry` (notation は宣言だけ) で書き、`lake env lean Common2026/Shannon/TypedRV.lean` が **silent + sorry warning のみ** になることを Phase 1 の Done 条件とする。

```lean
import Common2026.Shannon.Bridge
import Common2026.Shannon.MutualInfo
import Common2026.Shannon.CondMutualInfo
import Common2026.Fano.Measure
import Common2026.Shannon.DifferentialEntropy
import Mathlib.InformationTheory.KullbackLeibler.Basic

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β γ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Re-export `MeasureFano.condEntropy` into `InformationTheory.Shannon` namespace. -/
abbrev condEntropy := @InformationTheory.MeasureFano.condEntropy

/-- KL divergence between two random variables (typed RV form, 1-measure).
    See [in-source docstring] for the design choice (1-measure vs 2-measure). -/
noncomputable def klDivRV (μ : Measure Ω) (X Y : Ω → α) : ℝ≥0∞ :=
  klDiv (μ.map X) (μ.map Y)

lemma klDivRV_def (μ : Measure Ω) (X Y : Ω → α) :
    klDivRV μ X Y = klDiv (μ.map X) (μ.map Y) := by sorry

/-- Differential entropy of a real-valued random variable (typed RV form). -/
noncomputable def differentialEntropyRV (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  differentialEntropy (μ.map X)

lemma differentialEntropyRV_def (μ : Measure Ω) (X : Ω → ℝ) :
    differentialEntropyRV μ X = differentialEntropy (μ.map X) := by sorry

-- notation (Phase 3 で確定):
scoped[InformationTheory.Shannon] notation3:50 "H(" X ")"           => entropy _ X
scoped[InformationTheory.Shannon] notation3:50 "H(" X " | " Y ")"   => condEntropy _ X Y
scoped[InformationTheory.Shannon] notation3:50 "I(" X " ; " Y ")"   => mutualInfo _ X Y
scoped[InformationTheory.Shannon] notation3:50 "I(" X " ; " Y " | " Z ")" => condMutualInfo _ X Y Z
scoped[InformationTheory.Shannon] notation3:50 "D(" X " ‖ " Y ")"   => klDivRV _ X Y

end InformationTheory.Shannon
```

**各項目で参照する既存補題 (在庫 §A〜D)**:

| 項目 | 既存定義 / 補題 | file:line |
|---|---|---|
| `condEntropy` abbrev | `InformationTheory.MeasureFano.condEntropy` | `Common2026/Fano/Measure.lean:68` |
| `klDivRV` def | `klDiv` (Mathlib) | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` |
| `klDivRV_def` | `rfl` で済む (定義展開) | — |
| `differentialEntropyRV` def | `differentialEntropy` | `Common2026/Shannon/DifferentialEntropy.lean:42` |
| `differentialEntropyRV_def` | `rfl` で済む | — |
| notation `H(X)` | `entropy` | `Common2026/Shannon/Bridge.lean:43` |
| notation `H(X|Y)` | `condEntropy` (= 上記 abbrev) | `Common2026/Fano/Measure.lean:68` 経由 |
| notation `I(X;Y)` | `mutualInfo` | `Common2026/Shannon/MutualInfo.lean:36` |
| notation `I(X;Y|Z)` | `condMutualInfo` | `Common2026/Shannon/CondMutualInfo.lean:46` |
| notation `D(X‖Y)` | `klDivRV` (新規) | 本ファイル |

**bridge ヘルパー (新規追加分)**: ゼロ件。在庫 §C で確認した既存 bridge (`Measure.map_apply`, `isProbabilityMeasure_map`, `integral_map`, `klDiv_map_measurableEquiv`) で十分。**Phase 3 のサンプル `example` で 1 本足りないと判明したら、そこで追加判断する**。

---

## F. Phase 切り分け

### Phase 1: skeleton + silent
- 上記 E の内容を `Common2026/Shannon/TypedRV.lean` に Write
- `Common2026.lean` に `import Common2026.Shannon.TypedRV` 追記
- `lake env lean Common2026/Shannon/TypedRV.lean` が silent + sorry warning のみ
- **proof-log**: no (skeleton 段階)
- 工数: 30 分

### Phase 2: alias / re-export 充填
- `klDivRV_def` / `differentialEntropyRV_def` を `rfl` 1 行で割る
- `abbrev condEntropy` は Phase 1 で既に sorry-free (定義のみ、補題なし)
- 工数: 15 分
- **proof-log**: no
- Done: `lake env lean Common2026/Shannon/TypedRV.lean` が silent + sorry 0 個

### Phase 3: notation 宣言 + 1 文字衝突解消 + サンプル `example`
- まず `rg`/`loogle` で **`H` / `I` / `D` の 1 文字識別子の衝突**を確認:
  - `rg "^def H\b|^abbrev H\b|notation .*\"H\\(" .lake/packages/mathlib/Mathlib/InformationTheory` 等
  - `loogle "H _"` も併用
  - 衝突なし → notation 宣言をそのまま投入
  - 衝突あり → 撤退ライン §H-2 (添字付き `Hₛ` / `Iₛ` / `Dₛ` または `H[X]` / `I[X;Y]` / `D[X‖Y]` への縮退)
- notation 宣言を `Common2026/Shannon/TypedRV.lean` に追加
- **動作確認 `example` を 1 個書く**:

```lean
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : Ω → α) (hX : Measurable X) :
    0 ≤ H(X) := by
  exact entropy_nonneg μ X hX
```

(または `H(X | Y)` / `I(X;Y)` / `D(X‖Y)` のいずれか 1 つで似た形。最低 1 つの notation が動くことを示せばよい)
- 工数: 30〜60 分 (衝突確認 + notation 投入 + example で消耗)
- **proof-log**: yes (notation 設計の確定 / 衝突有無 / `notation3` で `μ` placeholder が効いたか効かなかったかを記録)
- Done: `lake env lean Common2026/Shannon/TypedRV.lean` silent、`H(X)` / `H(X|Y)` / `I(X;Y)` / `I(X;Y|Z)` / `D(X‖Y)` の **5 つ全ての notation が elaborate に通る**

### Phase 4: verify + regression check
- `lake env lean Common2026/Shannon/TypedRV.lean` 0 error / 0 sorry / warning 最小
- 既存 0 sorry ファイルへの **regression なし**を確認:
  - `lake env lean Common2026/Shannon/Bridge.lean` silent
  - `lake env lean Common2026/Shannon/MutualInfo.lean` silent
  - `lake env lean Common2026/Shannon/CondMutualInfo.lean` silent
  - `lake env lean Common2026/Fano/Measure.lean` silent
  - `lake env lean Common2026/Shannon/DifferentialEntropy.lean` silent
- (必要なら `lake build Common2026.Shannon.TypedRV` で olean 焼き)
- 工数: 15〜30 分
- **proof-log**: yes (合流 + メトリクス: 行数 / 新規 def 数 / notation 数 / Phase 3 で衝突確認した識別子のメモ)
- Done: 全ファイル silent、proof-log 完備

**~~Phase 5 (callsite migration / 既存ファイルへの notation 適用)~~** — 本タスクの範囲外 (ユーザー確認済)。後続 seed (T2-A AWGN, T3-B MAC, T1-A Huffman 等) が自身の callsite で `open InformationTheory.Shannon` する形で取り込む。

---

## G. 判定条件 (Definition of Done)

1. `lake env lean Common2026/Shannon/TypedRV.lean` が **0 error / 0 sorry / 警告最小** で silent
2. **notation 5 つすべて (`H(X)` / `H(X|Y)` / `I(X;Y)` / `I(X;Y|Z)` / `D(X‖Y)`) が動く** — `Common2026/Shannon/TypedRV.lean` 末尾の `example` ブロックで証明済み (`open InformationTheory.Shannon` 下)
3. **既存 0 sorry ファイルが regression なし** — 上記 §F Phase 4 の 5 ファイル + `Common2026/Shannon/Han.lean` / `HanD.lean` / `AEP.lean` 等が `lake env lean` で silent
4. `Common2026.lean` に `import Common2026.Shannon.TypedRV` 追記済み
5. proof-log (`docs/proof-log-typed-rv.md` 等) に **Phase 3 で確認した衝突有無 / `notation3` の `μ` placeholder 挙動 / 採用した最終 notation の verbatim** を記録

---

## H. 撤退ライン

> 在庫 §G で「発動シナリオ不明」と記述したが、Phase 3 着手時に顕在化しうるリスクを 3 つ列挙して撤退条件を確定する。

### H-1. **bridge lemma が 1 本以上必要だと判明** (Phase 3 の `example` で詰まる)

- 判定: Phase 3 のサンプル `example` を 1 つも書けない (notation 展開後に `rfl` / 既存補題で割れない)
- 撤退: **本タスクの範囲を「notation 5 つ + alias 2 個 + abbrev 1 個 + bridge lemma 必要分」に拡大**し、必要 bridge を 1〜3 本だけ追加して Phase 4 を再評価する。**4 本以上必要**になった場合は I-1 を Phase A (notation + alias のみ) / Phase B (bridge lemma 群) に分割、本 plan は Phase A までで close + Phase B を別 plan に切り出す

### H-2. **`H` / `I` / `D` の 1 文字 notation が Mathlib / Std で衝突**

- 判定: Phase 3 着手時 `rg`/`loogle` で衝突を発見、または notation 投入後 `lake env lean` でパースエラー
- 撤退: 縮退選択肢を順に試す:
  1. **添字付き形** `Hₛ(X)` / `Iₛ(X;Y)` / `Dₛ(X‖Y)` (`scoped[InformationTheory.Shannon]` でさらに限定)
  2. **角括弧形** `H[X]` / `I[X;Y]` / `D[X‖Y]` (Mathlib `IndepFun` の `⟂ᵢ[μ]` precedent)
  3. **`μ` 明示形** `H[μ; X]` / `I[μ; X, Y]` / `D[μ; X ‖ Y]` (`notation3` で `μ` placeholder が効かなかった場合の自然な fallback)
- 縮退判定は **Phase 3 開始時に確定**して proof-log に記録。途中で 1 → 2 → 3 と滑らせない (確定後は固定)

### H-3. **`notation3` で `μ` を `_` placeholder にできない**

- 判定: Phase 3 で `notation3:50 "H(" X ")" => entropy _ X` を投入したが、`_` の elaboration が通らない / `μ` が明示で要求される
- 撤退: H-2 の 3 番 (`μ` 明示形) に縮退、または **`abbrev H (μ : Measure Ω) ...` を立てて notation を `H_[μ] X` のような 2 段形にする**。後者は 1 段増えるが教科書 `H(X)` への近さは保つ
- 工数増加: 30 分以内なら容認、それ以上なら H-2 の 1 番 (添字付き) に逆戻し

### H-4. **`klDivRV` で 2 測度版も publish したくなる** (後続 seed からの要求が plan 起草時点で見えていなかった)

- 判定: 本 plan 起草後、Phase 3 までに hypothesis testing 系 seed (Chernoff T1-B / Hoeffding T1-D) で 2 測度版要求が確定的に見える
- 撤退: 2 測度版 `klDivRV₂ (μ : Measure Ω) (ν : Measure Ω') (X : Ω → α) (Y : Ω' → α) := klDiv (μ.map X) (ν.map Y)` を **追加** publish (1 測度版は不変)。notation `D(X‖Y)` は 1 測度版に bind したまま、2 測度版は notation なしで呼ぶ。本 plan の C-1 確定を **判断ログに append** で update

---

## I. 規模見積もり

| 指標 | 見積もり |
|---|---|
| 新規 Lean 行数 | 50〜80 行 (1 ファイル) |
| 新規 `def` 数 | 2 (`klDivRV`, `differentialEntropyRV`) |
| 新規 `abbrev` 数 | 1 (`condEntropy` 再エクスポート) |
| 新規 `lemma` 数 | 2 (`klDivRV_def`, `differentialEntropyRV_def`、両者 `rfl`) |
| 新規 notation 数 | 5 (`H(X)` / `H(X|Y)` / `I(X;Y)` / `I(X;Y|Z)` / `D(X‖Y)`) |
| サンプル `example` 数 | 1 以上 (notation 5 つすべて elaborate) |
| ターン見積もり | 1〜2 セッション (Phase 1 + 2 で 1 セッション、Phase 3 + 4 でもう 1 セッション) |
| 実装時間 | 1.5〜3 時間 (Phase 1: 30 分、Phase 2: 15 分、Phase 3: 30〜60 分、Phase 4: 15〜30 分、撤退ライン発動時 +1 時間) |
| 撤退ライン §H-1 (bridge lemma 1〜3 本追加) 発動時 | +1〜2 時間、+30〜50 行 |
| 撤退ライン §H-2 (notation 縮退) 発動時 | +30 分、行数増減なし |

**新数学なし**。在庫が示した通り「notation + 2 alias + 1 abbrev」で本体は終わる。

---

## J. 後続 seed への影響メモ

### I-1 → I-2 (General DMC capacity)

`BlockwiseChannel` 抽象を立てる際、`H(X^n)` / `H(Y^n)` / `I(X^n; Y^n)` の typed RV 形が使えると statement の見た目が教科書 `capacity = lim_n (1/n) max I(X^n; Y^n)` と完全一致する。I-1 の notation を `open InformationTheory.Shannon` で取り込む。具体的には I-2 の `capacity_lim` 定義が:

```lean
noncomputable def capacity_lim (W : BlockwiseChannel α β) : ℝ :=
  Filter.atTop.limsup (fun n => (1 / n) * ⨆ p, (I(X^n[p] ; Y^n[p; W])).toReal)
```

のように書ける (`X^n[p]` / `Y^n[p; W]` は I-2 側で別途定義する典型 RV)。

### I-1 → I-3 (Asymptotic / exponent framework)

`\doteq` (exponent equality) を `Tendsto ((1/n) * log ...) atTop (𝓝 (- exponent))` 形で定義する際、`exponent` 部分が `D(μ ‖ ν)` (Stein) / `I(X;Y)` (channel coding) / `D(X‖Y)` (typed RV 形) で書き分けたい。I-1 の `D(X‖Y)` notation が typed RV 形での `\doteq` 表現を支える。

### I-1 → T1-A (Huffman) / T1-B (Chernoff) / T2-A (AWGN) / T3-B (MAC) etc.

すべての後続 seed が `open InformationTheory.Shannon` 1 行で typed RV notation を取り込む。**callsite migration の自然な発生源は後続 seed 側** であり、本 I-1 タスクは取り込み準備までで close する。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-18 起草**: 在庫調査 `typed-rv-mathlib-inventory.md` 完了後の plan 起草。設計判断 §C-1〜4 を確定:
   - C-1 `klDivRV` 1 測度版のみ publish
   - C-2 notation `scoped[InformationTheory.Shannon] notation3` + precedence 50 + `H(X)` / `H(X|Y)` / `I(X;Y)` / `I(X;Y|Z)` / `D(X‖Y)` の 5 つ
   - C-3 `MeasureFano.condEntropy` → `Shannon.condEntropy` への `abbrev` 再エクスポート 1 行
   - C-4 5 型クラスの束ねクラスは作らない (Mathlib 慣習維持)
   
   撤退ラインを §H-1〜4 の 4 シナリオで具体化。規模 50〜80 行 / 1〜2 セッション / 1.5〜3 時間。

2. **2026-05-18 Phase 3 実装中 — precedence 50 → `:max` への変更 (撤退ライン §H-2 周辺)**: C-2 の `notation3:50` precedent (Mathlib `IndepFun` `⟂ᵢ[μ]` 由来) は、`0 ≤ H(...)` のように `≤` (precedence 50) の右辺で notation を使うと **「unexpected token at this precedence level」エラー** で破綻することが実機判明。Lean parser は `≤` の右辺で precedence > 50 の term を期待するため、`notation3:50` の `H(...)` 全体は適合しない。**`notation3:max` に変更** で `H(...)` を atomic な高 precedence term として扱うことで解決 (Mathlib 内も `Norm.norm` 等で `:max` を採用)。教科書記法から離れる縮退ではなく、precedence 値だけの修正で済んだ。

3. **2026-05-18 Phase 3 実装中 — `notation3` `_` placeholder NG (撤退ライン §H-3 発動)**: C-2 で「`notation3` で `μ` を `_` placeholder にできるか Phase 3 で実機確認」と保留していたが、実機で **`don't know how to synthesize placeholder for argument μ`** エラー。原因: `example : <type with H(X)> := <body>` の型注釈位置では body 情報が使えず `μ` 推論ができない (Mathlib `IndepFun` の volume 版がうまく動くのは `volume` がハードコードされたデフォルトだから)。撤退ライン §H-3 に従い **`μ` 明示形** に縮退:
   - `H(μ; X)` for `entropy μ X`
   - `H(μ; X | Y)` for `condEntropy μ X Y`
   - `I(μ; X ; Y)` for `mutualInfo μ X Y`
   - `I(μ; X ; Y | Z)` for `condMutualInfo μ X Y Z`
   - `D(μ; X ∥ Y)` for `klDivRV μ X Y`
   
   教科書 `H(X)` から `H(μ; X)` への 1 段増だが、Mathlib `IndepFun` `X ⟂ᵢ[μ] Y` precedent と整合。**`D(X ‖ Y)` の `‖` (U+2016) は norm token `‖x‖` と衝突するため `∥` (U+2225 Parallel To) に置換**。editor 表示は近似だが意味は完全保存。

4. **2026-05-18 Phase 4 verify 完了**: `lake env lean Common2026/Shannon/TypedRV.lean` silent (184 行 / 0 sorry / 0 error)。regression check 7 ファイル (`Bridge` / `MutualInfo` / `CondMutualInfo` / `Fano/Measure` / `DifferentialEntropy` / `Han` / `AEP`) 全て exit 0、warning は既存のもののみ (本タスク起因 0)。bridge lemma 新規追加ゼロを維持。判断ログ 2, 3 で確定した notation 形 (5 つ) を最終採用。

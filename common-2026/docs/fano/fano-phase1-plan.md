# Phase 1: Markov 形 Fano への拡張・マイルストーン計画

> ムーンショット全体計画は `docs/fano/fano-moonshot-plan.md`。本ファイルはその Phase 1 の詳細。

## Context

### Phase 0 の現状

`Common2026/Fano/Core.lean` に、外部仮定なしで通っている形：

```
H(X | Y) ≤ h(Pe) + Pe · log(|X| − 1)
  where  X, Y : Fintype（離散・有限）
         decode : Y → X（決定論的）
         Pe = ∑ {(x, y) : x ≠ decode y}, P(x, y)
```

主要な道具立て：

- `FiniteJointPMF X Y`（自前構造体、`mass : X → Y → ℝ`、非負・総和 1）
- `errIndicator decode x y := decide (x ≠ decode y)`
- `withErr decode : X → Bool → Y → ℝ`（`(X, E, Y)` の 3 変数質量）
- `Joint3` 名前空間でのチェインルール 2 通り
- 単項エントロピーの最大値補題 (`sum_negMulLog_sub_le_sum_mul_log_card`)

### Phase 1 のゴール

Cover & Thomas Thm 2.10.1 の教科書形：

```
H(X | X̂) ≤ h(Pe) + Pe · log(|X| − 1)
  where  X, X̂ : Fintype（離散・有限）
         joint PMF P on (X, X̂) は任意（X̂ は決定論的関数とは限らない）
         Pe = ∑ {(x, x̂) : x ≠ x̂}, P(x, x̂)
```

これにより Phase 0 の `decode : Y → X` 形は、Markov chain `X → Y → X̂` で
`X̂ = decode(Y)` と取った特殊化として、データ処理不等式（DPI）経由で導出される。

### 非ゴール

- Markov chain の一般形（`X̂` が `Y` の確率的関数）の data processing inequality 全般
- `H(X) − H(X | Y) = I(X; Y)` などの mutual information 整備
- `PMF`（可算離散）化（これは Phase 2/3 の話）

---

## Approach

**戦略: 既存の `Fano/Core.lean` を `(X, X̂)` Markov 形に in-place リファクタし、Phase 0 形（`decode : Y → X` 版）を DPI 経由の薄いラッパーとして残す。**

戦略上の鍵:

1. **証明本体はほぼ機械的**。現 `errIndicator decode x y := decide (x ≠ decode y)` を
   `errIndicator x x̂ := decide (x ≠ x̂)` に置き換えるだけで、`withErr` / `Joint3` /
   per-term bound の構造はすべて生きる。`Y` を `X̂` に rename するだけ。
2. **真に新しい仕事は DPI のみ**。「`X̂ = f(Y)` の場合、`H(X | Y) ≤ H(X | X̂)`」を
   `negMulLog` の凹性 + Jensen から証明する。これが Phase 1 の唯一の非自明部分。
3. **座標非依存の wrapper（`Fano.lean` 中の `fano_inequality_of_le_qaryEntropy` 等）はそのまま**。
   `FiniteJointPMF` 名前空間の `errorProb decode` / `fano_inequality_of_core` 系のみ書き換え。
4. **`Fano/Entropy.lean` / `Fano/CondEntropy.lean` / `Fano/BinaryJensen.lean` は不変**。
   これらは座標非依存の道具箱なので Phase 1 で触る理由がない。

---

## ファイル構成

Phase 1 終了時の状態：

```
Common2026/
  Fano.lean                  ← Markov 版 wrapper + Phase 0 形は decode wrapper として残す
  Fano/
    Entropy.lean             ← 不変
    CondEntropy.lean         ← 不変
    BinaryJensen.lean        ← 不変
    Core.lean                ← (X, X̂) Markov 形に書き直し
    DPI.lean                 ← 新規。Pushforward と data processing inequality
```

`Common2026.lean`（library root）に `import Common2026.Fano.DPI` を追記。

---

## マイルストーン

### P1-M0. 監査と Phase 0 流用範囲の確定（半日）

リファクタの境界線を確定する。

- `Fano/Core.lean` の各定理を「rename だけで通るか / 中身に手を入れる必要があるか」で分類。
  - 期待: ほぼ全部前者。`Y` → `X̂`、`decode : Y → X` を引数から削除、`errIndicator decode x y` → `errIndicator x x̂`、`errorProb decode` → `errorProb` の 4 種の置換でほぼ済むはず。
- `Fano.lean` の wrapper 定理を 3 群に分類：
  - **座標非依存群**: `fanoBoundRHS`, `qaryEntropy_eq_fanoBoundRHS`, `fano_inequality_of_le_qaryEntropy`, `fano_inequality_of_alphabet`, `fano_error_lower_bound_of_*` → 不変
  - **`FiniteJointPMF` Markov 化対象**: `errorProb decode`, `fano_inequality_of_core`, `error_lower_bound_of_core`, `fano_inequality`, `error_lower_bound` → 書き換え
  - **Phase 0 互換用に残す**: 上の旧形を DPI 経由で再構成する別名（命名は P1-M4 で決定）
- DPI に必要な Mathlib API を確認：
  - `Real.concaveOn_negMulLog`（Phase 0 で利用済み）
  - `Real.negMulLog_nonneg` / `Real.negMulLog_zero`（同）
  - 有限 Jensen（`Fano/Entropy.lean` と `Fano/BinaryJensen.lean` のものが使える）

**Done 条件**: 「P1-M1 で何 line 動かすか」「P1-M3 で証明する補題のシグネチャ」が紙に書き出せる。

---

### P1-M1. `Fano/Core.lean` を Markov 形にリファクタ（1〜2 日）

**Subject of refactor**: `Fano/Core.lean` 全体（446 行）。

機械的な置換 4 種：

| 旧 | 新 |
|---|---|
| 型変数 `Y` | `X̂` |
| `decode : Y → X` | （削除） |
| `errIndicator decode x y := decide (x ≠ decode y)` | `errIndicator x x̂ := decide (x ≠ x̂)` |
| `errorProb decode` | `errorProb`（引数なし） |

期待される最終形（抜粋）：

```lean
namespace InformationTheory.FiniteJointPMF

variable {X X̂ : Type*} [Fintype X] [Fintype X̂] [DecidableEq X]

def errIndicator : X → X̂ → Bool := fun x x̂ => decide (x ≠ x̂)

def errorProb (P : FiniteJointPMF X X̂) : ℝ :=
  ∑ x, ∑ x̂, if x = x̂ then 0 else P.mass x x̂

def withErr (P : FiniteJointPMF X X̂) : X → Bool → X̂ → ℝ :=
  fun x e x̂ => if e = errIndicator x x̂ then P.mass x x̂ else 0

theorem fano_core (P : FiniteJointPMF X X̂) (hcard : 2 ≤ Fintype.card X) :
    P.condEntropy ≤ Real.qaryEntropy (Fintype.card X) P.errorProb := ...
```

**`X̂` の DecidableEq 要否に注意**: 現コードは `[DecidableEq X]` のみだが、
`errIndicator x x̂ := decide (x ≠ x̂)` で `x ∈ X` と `x̂ ∈ X̂` の比較が要るので、
**`X` と `X̂` を同型とみなして `X̂ := X` に固定する**のが現実的。
（Cover-Thomas もそうしているし、`x = x̂` を意味的に語るには両者は同じアルファベット。）

→ 結論: `FiniteJointPMF` の第 2 引数を `X` に再利用 (`P : FiniteJointPMF X X`) する形に統一。
`X̂` は型ではなく**変数名上の記号 / docstring 上の概念**として残す。

**Done 条件**:
- `lake env lean Common2026/Fano/Core.lean` が silent
- 主定理 `fano_core (P : FiniteJointPMF X X) ...` が通る
- 旧 `Fano/Core.lean` の `decode : Y → X` 引数がコードベースから消えている

---

### P1-M2. `Fano.lean` の wrapper を Markov 形に追従（半日）

`Fano.lean` の `FiniteJointPMF` 名前空間以下を Markov 化：

- `fano_inequality_of_core (P : FiniteJointPMF X X) (hcore : ...)`: `decode` 引数削除
- `error_lower_bound_of_core`: 同上
- `fano_inequality (P : FiniteJointPMF X X) (hcard : ...)`: 同上
- `error_lower_bound`: 同上

座標非依存群（`fano_inequality_of_le_qaryEntropy` 等）は変更不要。

**Done 条件**:
- `lake env lean Common2026/Fano.lean` が silent
- Markov 形の `fano_inequality` / `error_lower_bound` がトップレベルで使える状態

---

### P1-M3. Pushforward と DPI（1〜2 日）

**新規ファイル `Common2026/Fano/DPI.lean`**。

Phase 1 で唯一の非自明な数学的内容。

#### P1-M3-a. Pushforward の定義（30 分）

```lean
namespace InformationTheory.FiniteJointPMF

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- f : Y → X̂ による (X, Y) joint PMF の pushforward。-/
def pushforward (P : FiniteJointPMF X Y) {X̂ : Type*} [Fintype X̂] [DecidableEq X̂]
    (f : Y → X̂) : FiniteJointPMF X X̂ where
  mass x x̂ := ∑ y ∈ {y | f y = x̂}.toFinset, P.mass x y
  mass_nonneg := by ...
  sum_mass := by ...
```

Mathlib の `Finset.filter` を使うほうが綺麗かもしれない。実装時に決める。

#### P1-M3-b. Pushforward 下での `errorProb` の対応（30 分）

```lean
/-- Phase 0 の errorProb decode と Phase 1 の pushforward errorProb の同一視。-/
lemma pushforward_errorProb_eq_decode_errorProb
    (P : FiniteJointPMF X Y) (decode : Y → X) :
    (P.pushforward decode).errorProb = (...) := ...
```

ここで右辺は Phase 0 の `errorProb decode` の和だが、Phase 1 で `errorProb` は引数なしになっているので、対応関係を補題として明示する。

#### P1-M3-c. DPI 本体（1〜1.5 日）

```lean
/-- データ処理不等式（決定論的後処理版）:
    f : Y → X̂ による pushforward は条件付きエントロピーを増やす。-/
theorem condEntropy_le_pushforward_condEntropy
    (P : FiniteJointPMF X Y) {X̂ : Type*} [Fintype X̂] [DecidableEq X̂]
    (f : Y → X̂) :
    (P.pushforward f).condEntropy ≥ P.condEntropy := ...
```

証明は `negMulLog` の凹性 + Jensen：

1. `H(X | X̂) = ∑_{x̂} P_X̂(x̂) · H(X | X̂=x̂)`
2. `P(x | x̂) = ∑_{y : f(y)=x̂} (P_Y(y)/P_X̂(x̂)) · P(x | y)` （凸結合）
3. `negMulLog` の凹性 + Jensen で `H(X | X̂=x̂) ≥ ∑_{y : f(y)=x̂} (P_Y(y)/P_X̂(x̂)) · H(X | Y=y)`
4. `x̂` で和を取って `H(X | X̂) ≥ ∑_y P_Y(y) · H(X | Y=y) = H(X | Y)`

**ハマる可能性のあるポイント**:
- 条件付き分布 `P(x | y) := P(x, y) / P_Y(y)` を `P_Y(y) = 0` の場合にどう扱うか
  → `P_Y(y) = 0` のときは `H(X | Y=y)` を 0 にする規約で逃げる（Phase 0 と同じ）
- `Finset` 上のグルーピング（`f` のファイバごとの和）の補題探し
  → `Finset.sum_fiberwise` 系を使う
- Jensen を「重み付き和の凹関数」に適用するときの `[Decidable]` instance 周り

**Done 条件**:
- `lake env lean Common2026/Fano/DPI.lean` が silent
- `condEntropy_le_pushforward_condEntropy` の signature が上の通り

---

### P1-M4. Phase 0 形を Markov + DPI から復元（半日）

`Common2026/Fano.lean` の末尾に Phase 0 互換 wrapper を追加：

```lean
namespace InformationTheory.FiniteJointPMF

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]

/-- Phase 0 形: decode : Y → X による Fano。Markov 形 + DPI から導出。-/
theorem fano_inequality_decode
    (P : FiniteJointPMF X Y) (decode : Y → X)
    (hcard : 2 ≤ Fintype.card X) :
    P.condEntropy ≤ fanoBoundRHSOfAlphabet X ((P.pushforward decode).errorProb) := by
  have hDPI := P.condEntropy_le_pushforward_condEntropy decode
  have hFano := (P.pushforward decode).fano_inequality hcard
  linarith

/-- 同上、誤り確率を Phase 0 直接形で書いたバージョン。-/
theorem fano_inequality_decode'
    (P : FiniteJointPMF X Y) (decode : Y → X)
    (hcard : 2 ≤ Fintype.card X) :
    P.condEntropy ≤ fanoBoundRHSOfAlphabet X
      (∑ x, ∑ y, if x = decode y then 0 else P.mass x y) := by
  rw [← P.pushforward_errorProb_eq_decode_errorProb decode]
  exact P.fano_inequality_decode decode hcard

/-- Phase 0 の error_lower_bound に対応する decode 版。-/
theorem error_lower_bound_decode (P : FiniteJointPMF X Y) (decode : Y → X) ... := ...
```

各 wrapper は **5 行以内**を目標。10 行を超えるなら DPI の API が足りていないサイン。

**Done 条件**:
- 上記 3 wrapper が `lake env lean` で silent
- 各 wrapper の証明が機械的（DPI + Markov Fano + linarith / rw）

---

### P1-M5. クリーンアップ + proof-log + metrics（半日）

- `Common2026.lean` に `import Common2026.Fano.DPI` を追記
- 全ファイル `lake env lean` で silent 確認:
  - `Common2026/Fano.lean`
  - `Common2026/Fano/Core.lean`
  - `Common2026/Fano/DPI.lean`
  - `Common2026/Fano/Entropy.lean` / `CondEntropy.lean` / `BinaryJensen.lean`（不変だが念のため）
- 旧 `decode` 引数の残骸（コメントアウトされた古いコード等）を削除
- `scripts/session_metrics.ts` を回して metrics を取得
- `proof-log` skill を起動して `docs/proof-logs/proof-log-fano-phase1.md` と `docs/metrics/fano-phase1.{manifest,metrics}.{json,md}` を生成

**Done 条件**:
- 全ファイル silent
- proof-log と metrics が `docs/` に揃っている
- Phase 1 の作業時間・ツールコール数が記録されている

---

## 全体の工数感

| マイルストーン | 工数 |
|---|---|
| P1-M0 監査 | 半日 |
| P1-M1 Core.lean リファクタ | 1〜2 日 |
| P1-M2 Fano.lean 追従 | 半日 |
| P1-M3 DPI | 1〜2 日 |
| P1-M4 Phase 0 復元 | 半日 |
| P1-M5 クリーンアップ + ログ | 半日 |

合計: **3〜5 日**（人間 + Claude Code 共同作業の壁時計時間）。

P1-M1 と P1-M3 が主要リスク。前者は機械的だが量が多く、後者は数学的に新規。
P1-M3 で 3 日以上溶けるようなら、Phase 1 のスコープ自体を見直す（DPI を後回しにして Markov 形だけ完成 → Phase 0 形は当面残す、という縮退案）。

---

## 撤退ライン

- P1-M1 で 3 日以上溶ける → リファクタ範囲を狭める（`FiniteJointPMF` 名前空間内だけ書き換え、`Fano.lean` の wrapper はそのまま `decode` 引数を引きずらせる）
- P1-M3 で 3 日以上溶ける → DPI を将来課題に切り出し、Phase 1 は「Markov 形の Fano + Phase 0 は独立に併存」で打ち止め（Approach B 相当の中間形）
- どちらも proof-log には**正直に**記録する。デモの貴重なデータ。

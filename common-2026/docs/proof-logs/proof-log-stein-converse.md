# Stein 補題 converse 半分 (Phase A〜B) — ボトルネック分析

将来 (a) Mathlib 不在の Pi 化情報量補題 (KL / mutual info の i.i.d. n 倍) の自動 induction 補助、(b) 「DPI + 数値情報量補題」の組み合わせで Bernoulli 専用補題を回避する設計パターン認識、を判断するベースライン記録。

**定量データ**: 本 Track は Track 1 / Track 2 と同 session / 同 prompt_id 内のサブエージェント起動として実行されたため、3 Track 合算の metrics として記録。Track 単独抽出は不可。同 session 全体は [docs/metrics/stein-converse.metrics.md](../metrics/stein-converse.metrics.md) を参照 (Track 1 metrics と内容重複)。本ファイルは定性記録に集中する。

## 0. 対象問題と成果物

`docs/moonshot-seeds.md` 「A. 直接 deferred」項目 "Stein converse (Phase C/D)" の Phase A〜B 本実装。Stein achievability (`Common2026/Shannon/Stein.lean` Phase A〜B、別セッション完了) の対偶半分:

```
任意検定 A_n ⊆ α^n、type-I error α_n := P^n(A_n^c) ≤ ε に対し
  -(1/n) * log Q^n(A_n) ≤ (1/(1-ε)) * (klDiv P Q + h(ε)/n)
                                                    -- Cover-Thomas 11.8.3
```

Phase C (`Tendsto` 形 `stein_lemma : Tendsto (fun n => -(1/n) * log (steinOptimalBeta P Q n ε)) atTop (𝓝 (klDiv P Q))`) は別 plan に分離 (新規数学なし、Filter / sInf API plumbing のみ、`docs/moonshot-seeds.md` A セクションに新規 deferred として登録)。

成果物:

- `Common2026/Shannon/Stein.lean` (+497 行 → 累計 ~1123 行) — Phase A: `klDiv_pi_eq_n_smul` (Pi 化 KL chain rule、98 行 induction) / Phase B: Bool 上 sum 形 + `mul_log_le_toReal_klDiv` 下界 + α-level + sign 解析 → `stein_converse_finite_n` (concrete inequality with `1/(1-ε)` correction)
- `Common2026/Shannon/DPI.lean` (1 行) — `klDiv_map_le` を `private` から public 化 (caller `mutualInfo_le_of_postprocess` のみ、破壊リスクゼロ)
- `lake env lean Common2026/Shannon/Stein.lean` / `Common2026/Shannon/DPI.lean` 共に silent
- `lake build Common2026.Shannon.Stein` 通過 (2758/2758)
- 行数 +497 は plan target 290〜530 内、上限近傍

## 1. 問題のキャラクター

「Pi 化情報量補題が Mathlib に不在」+「DPI + 既存数値補題の合成で Bernoulli 専用補題を回避」の 2 軸が支配項。前者は 98 行 induction を自前で組む必要、後者は設計判断 (Bernoulli KL 閉形式を持ち込まず、Mathlib `mul_log_le_toReal_klDiv` 1 本で済ませる) の威力。

過去 proof-log との比較:
- 「Mathlib 不在 + 自前 induction」軸は Han Phase B ([proof-log-han-moonshot.md](proof-log-han-moonshot.md) の `jointEntropy_chain_rule_finRange` 65 行) と同型
- 「DPI + 数値補題で Bernoulli 専用回避」軸は本 Track が初例 (Sanov 等 LDP 系で再利用候補)

## 2. 数学的方針

### (Phase A) Pi 化 KL chain rule

`klDiv ((Measure.pi (fun _ => P)) : Measure (Fin n → α)) (Measure.pi (fun _ => Q)) = n • klDiv P Q`。`Fin n` 上の induction で `klDiv_compProd_eq_add` (Mathlib 既存 2-fold chain rule) を `MeasurableEquiv.piFinSuccAbove` で reshape して呼ぶ。base case (`n = 0`) は `Measure.pi_of_empty` + `klDiv_self`。

### (Phase B) DPI 経由の Bernoulli reduction

任意検定 `A_n ⊆ α^n` を Bool への Markov kernel `f := decide (· ∈ A_n) : (Fin n → α) → Bool` で post-process。DPI `klDiv_map_le`:

```
klDiv ((Measure.pi P).map f) ((Measure.pi Q).map f) ≤ klDiv (Measure.pi P) (Measure.pi Q) = n • klDiv P Q
```

Bool 上の post-DPI KL を `mul_log_le_toReal_klDiv` (Mathlib log-sum 下界) で展開すると、`P^n(A_n)` と `1 - P^n(A_n)` の log-sum 形下界が直接出る。Bernoulli KL の閉形式 `α log(α/β) + (1-α) log((1-α)/(1-β))` を陽に使わないのが鍵。

### (Phase B 後段) α-level + sign 解析

`P^n(A_n^c) ≤ ε` ⇒ `P^n(A_n) ≥ 1 - ε`。log-sum 下界の `(1-ε)` 倍 + `h(ε)` 上限 (Mathlib `binEntropy_le_log_two`) で `1/(1-ε)` 補正項込みの concrete inequality に到達。

数学的アイデアは Cover-Thomas 11.8 の標準論法 (新規ゼロ)。詰まりは proof tactic / Mathlib API surface の細部。

## 3. Mathlib 補題探索の実録

| 必要だったもの | クエリ | 試行 | 結果 |
|---|---|---|---|
| Pi 化 KL chain rule | loogle `klDiv (Measure.pi _) (Measure.pi _)` | 1 | **不在**。29 件の `klDiv` 補題に `pi` 含むものゼロ |
| `klDiv ≤ klDiv` 系 DPI | loogle `klDiv ≤ klDiv`, `klDiv_comp_le`, `klDiv_map` | 3 | Mathlib 不在、`fDiv` framework 自体不在 |
| Bernoulli KL 閉形式 | loogle `klDiv_bernoulli`, `binEntropy` | 2 | `binEntropy` は存在 (`binEntropy_le_log_two` 利用)、`klDiv_bernoulli` は不在 |
| log-sum 下界 (任意有限測度ペア) | loogle `mul_log_le_toReal_klDiv` | 1 | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:346` 発見 |
| Pi 値 absolute continuity | loogle `MeasureTheory.Measure.AbsolutelyContinuous.pi` | 1 | **不在**。自前 30 行構築 |
| `Subsingleton (Measure (Fin 0 → α))` | rg, loogle | 2 | 自動合成不可、`Measure.pi_of_empty` + `klDiv_self` で代替 |
| `Measure.compProd_const` の方向 | loogle `compProd_const` | 1 | `μ ⊗ₘ Kernel.const _ ν = μ.prod ν` 方向、reshape は `.symm` |

「Mathlib に無かった」もの:

- **Pi 化 KL chain rule** (`klDiv (Measure.pi _) (Measure.pi _) = n • klDiv P Q`) — 自前 98 行 induction (`klDiv_pi_eq_n_smul`)。`piFinSuccAbove` + 既存 `klDiv_map_measurableEquiv` (Common2026 内、本 Track 開始時点で既存) + `klDiv_prod_const_left` で組成。**上流 PR 候補**。
- **Pi 値 absolute continuity** (`(Measure.pi P) ≪ (Measure.pi Q) ↔ ∀ i, P i ≪ Q i`) — 自前 30 行 (`piFinSuccAbove` + `AbsolutelyContinuous.prod` induction)。**上流 PR 候補**。
- **DPI on KL** (集合関数 KL に対する `klDiv (κ ∘ μ) (κ ∘ ν) ≤ klDiv μ ν`) — Mathlib 不在、Common2026 既存 `Common2026/Shannon/DPI.lean:52` `klDiv_map_le` (`private` だった、本 Track で public 化)。Jensen + condExp で 50〜100 行構築済 (別セッション)。
- **`klDiv_bernoulli`** (Bernoulli KL 閉形式) — 不在だが回避可。`mul_log_le_toReal_klDiv` (任意有限測度ペアに対する log-sum 下界) を Bool 上に DPI で落としてから呼べば自動で Bernoulli の log-sum 下界が手に入る。**この設計判断が「Bernoulli 専用補題を持たないまま Stein converse を組める」核**。

## 4. 試行錯誤と後戻り

### 4.1 Pi 化 KL chain rule の base case で `Subsingleton` 自動合成失敗

**症状**: induction の `n = 0` ケースで `klDiv (Measure.pi (fun _ : Fin 0 => P)) (...) = 0 • klDiv P Q` を `Subsingleton (Measure (Fin 0 → α))` から導こうとしたが、typeclass 検索失敗。

**原因**: `Fin 0 → α` は `Subsingleton` だが、その上の `Measure` は `Subsingleton` ではない (中立 measure と zero measure が区別される)。型クラス検索の前提を勘違い。

**抜け方**: `Measure.pi_of_empty : Measure.pi μ = Measure.dirac (fun i => Empty.elim i.elim0)` で具体的な dirac measure に落とし、`klDiv_self : klDiv μ μ = 0` を経由。

**教訓**: `Subsingleton T` から `Subsingleton (Measure T)` への自動 lift は存在しない (中立 / zero の区別)。空集合上の measure は `Measure.pi_of_empty` / `Measure.dirac_of_isEmpty` で具体化するのが安全。

### 4.2 `Measure.compProd_const` の方向問題

**症状**: induction の `succ` ステップで `klDiv (Measure.pi (Fin (n+1) → α))` を `klDiv (P ⊗ₘ ...)` に reshape したかったが、`Measure.compProd_const : μ ⊗ₘ Kernel.const _ ν = μ.prod ν` は `compProd → prod` 方向で、求める方向の逆。

**抜け方**: `.symm` で逆向きに使う + Pi 値 measure を `.prod` 形に持ってきて reshape。

**教訓**: Mathlib lemma の方向 (定義 → 簡約形 / 簡約形 → 定義) は使用文脈に依存。`@[simp]` 方向と一致しない場合 `.symm` で逆走する判断を即座に。

### 4.3 `MeasureTheory.Measure.AbsolutelyContinuous.pi` 不在

**症状**: `(Measure.pi P) ≪ (Measure.pi Q)` を `klDiv` の前提として要求されたが、Mathlib に compositional lift 補題なし。

**抜け方**: 自前 30 行 (`piFinSuccAbove` + `AbsolutelyContinuous.prod` induction)。

**教訓**: Pi 値 measure 系 (Pi 値 KL chain rule、Pi 値 abs continuity、Pi 値 isFiniteMeasure 等) は Mathlib に系統的に薄い。Sanov / AEP / Stein 系のいずれを実装する時も同種の補題不在に当たる前提で plan すべき。Common2026 で蓄積した `Common2026/Shannon/Pi.lean` 系の補題群は Mathlib 上流化候補のクラスタ。

### 4.4 (期待されたトラブル) `(0 : Fin (k+1)).succAbove j = j.succ` defeq

**症状**: 期待されたトラブルが起きなかった事例。`succAbove` の使い方は Mathlib で reshape の鬼門になりがちだが、Pi family `fun _ => α` (constant family) で defeq が透過。

**抜け方**: 手動 reshape 不要。`rfl` か `simp` で潰れる。

**教訓**: `succAbove` の defeq 透過性は Pi family が定数か非定数かで激変する。constant family のときは defeq が強く、proof は短い。Stein は constant family (`fun _ => α`) なので運が良かった。

### 4.5 `binEntropy_le_log_two` で per-α `h(ε)` 依存を回避

**症状**: 当初 plan では `h(ε) = -ε log ε - (1-ε) log (1-ε)` の per-α (= per-ε) 評価を converse statement に持ち込む想定だった。これだと statement が ε に依存して見通しが悪い。

**抜け方**: Mathlib `binEntropy_le_log_two : binEntropy ε ≤ log 2` を使い、補正項を ε-非依存の上限 `log 2 / n` に置換。

**教訓**: 教科書 (Cover-Thomas 11.8) では `h(ε)/n` のまま残るが、Lean formalization では「ε 非依存上限」で済む場合は積極的に剥がした方が statement が clean。Mathlib の `binEntropy*` 系は `binEntropy_le_log_two` / `binEntropy_nonneg` 等が充実しているので活用余地あり。

### 4.6 `Bridge.lean` の `private klDiv_discrete_toReal_eq_sum` を duplicate

**症状**: Bool 上の KL を sum 形に展開する際、`Common2026/Shannon/Bridge.lean` の `private klDiv_discrete_toReal_eq_sum` が直接使えず、~50 行を `klDiv_bool_toReal_eq_sum` として Stein.lean 内に duplicate。

**抜け方**: duplicate (path of least resistance)。public 化リファクタは別 Track として保留。

**教訓**: `private` は file-scoped (CLAUDE.md 既載) のため、ファイルをまたぐ再利用には public 化必須。今回は Track 3 のスコープを小さく保つため duplicate を選んだが、3 番目の caller が現れた時点で `Common2026/Shannon/KLDivSum.lean` (仮) のような共通 helper module に lift すべき。Track 1 で `condEntropy_nonneg` を Pi.lean に lift した時と同じ判断軸。

## 5. ボトルネックではなかったもの

- **数学的アイデア**: Cover-Thomas 11.8 の標準論法。新規ゼロ。
- **achievability との接続**: Phase A〜B (achievability) は別セッションで完成済 (`stein_typical_set` 等の plumbing 既存)、converse 半分は achievability の plumbing を直接再利用せず独立に組めた。
- **`klDiv_compProd_eq_add` の発火**: 2-fold chain rule 自体は Mathlib 既存、Pi 化 induction で n 回呼ぶだけ。
- **`mul_log_le_toReal_klDiv` の発火**: log-sum 下界としての汎用性が高く、Bool 上でも具体測度を当てれば一発。
- **`lake env lean` の verification 速度**: 626 → 1123 行になっても per-file check は数秒。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたコスト |
|---|---|---|
| 高 | Pi 化情報量補題 (KL / mutual info / entropy の i.i.d. n 倍) の Mathlib 不在検出 + 自動 induction skeleton 生成 | Phase A 全体 (~98 行 / 数時間) |
| 高 | 「DPI + 数値補題で専用補題回避」設計パターンの認識 (Bernoulli KL を持ち込まず log-sum で代替) | plan 段階の設計判断、節約は質的 |
| 中 | Pi 値 measure 周辺補題群 (`AbsolutelyContinuous.pi`, `IsFiniteMeasure.pi` 等) の Mathlib 上流 PR 自動提案 | §4.3 の 30 行 + 将来の Sanov 系で再発防止 |
| 中 | `Subsingleton T` から `Measure T` の不可 lift の事前警告 | §4.1 の 1 つ目の dead-end |
| 中 | `private` 補題の cross-file 再利用判定 (3 番目の caller で public 化提案) | §4.6 の duplicate 50 行 |
| 低 | `succAbove` defeq の constant family 検出 (proof shortcut 提案) | §4.4 (1 fix) |
| 低 | `binEntropy_le_log_two` 等 Mathlib `binEntropy*` family の statement-level 上限置換提案 | §4.5 (statement clean-up) |

## 7. 補足

- 本 Track は orchestration (Track 1 → Track 2 → Track 3) の 3 番目で、同 session / 同 prompt_id 内のサブエージェント起動として実行。proof-log は Track 単位で分離、metrics は session 単位なので Track 3 単独抽出は不可。
- 上流 PR 候補 (本 Track 由来): `klDiv_pi_eq_n_smul` (Pi 化 KL chain rule)、Pi 値 `AbsolutelyContinuous.pi`、`klDiv_bernoulli` (任意 Bernoulli ペアの KL 閉形式)、`klDiv_map_le` (KL の DPI; Mathlib `fDiv` framework がない現状の代替)。
- Phase C (Tendsto/liminf 統合) は別 deferred。`stein_converse_finite_n` の `1/(1-ε)` 補正項を `n → ∞` で `inf_ε` 経由で absorb する `steinOptimalBeta` plumbing が中心、新規数学なし。
- 採らなかった代替案: (i) Bernoulli KL 閉形式を自前で書いて使う — `mul_log_le_toReal_klDiv` 経由が短いため不採用、(ii) `fDiv` framework を Common2026 内に新規構築して KL を inst — Stein 単体には過剰、(iii) Phase C (Tendsto 統合) を本 Track で続行 — 行数 +200 で 700 行超、context 圧迫リスクで別 plan に分離。

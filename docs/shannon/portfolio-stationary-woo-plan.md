# Portfolio: stationary market W_∞ AEP (CT 16.5.1 完全形) サブ計画

> **Parent**: [`portfolio-operational-plan.md`](portfolio-operational-plan.md) — Leg B 完全形 (deferral 分離)

Cover–Thomas *Elements of Information Theory* 2nd ed **§16.5 "Investment in Stationary Markets" Thm 16.5.1**
の完全形を standard B (0 sorry / 0 @residual / sorryAx-free / 独立 `@audit:ok`) まで形式化する。親 Leg B は
**fixed-b core** (固定 rebalance portfolio の成長率収束 + KT dominance) を proof-done 済。本計画は残る
**log-optimal `W_∞` AEP** = 因果 log-optimal 戦略の富の成長率が無限過去条件付き成長率 `W_∞` に収束する部分を負う。

**現状 = 未着手の honest deferral** (コード側に対応する `sorry` は無い = 捏造 statement 無し)。本計画は
scope 境界・要件・gateway-atom 案・壁リスクの記録であり、着手はまだ。

## 進捗 — 📋 未着手 (deferral)

- [ ] M0 在庫 — real-valued 条件付き growth / 可測選択 / Algoet–Cover sandwich の Mathlib / in-project 資産確定 📋
- [ ] R1 — 条件付き log-optimal portfolio の可測選択 📋 **gateway atom 第一候補**
- [ ] R2 — 条件付き成長率の単調収束 `W*(X_0 | X_{-1..−k}) ↑ W_∞` 📋
- [ ] R3 — real-valued SMB 級 AEP `(1/n) log S*_n → W_∞` 📋 **最リスク・別 gateway で早期壁判定**
- [ ] R4 — 組立 (CT 16.5.1 headline) + 配線 + 独立監査 📋

## ゴール / Approach

**ゴール** — 定常エルゴード市場 `{X_i}` (price-relative `X_i : Ω → Fin m → ℝ`、shift `T`) に対し、各時刻で
無限過去の条件付き log-optimal portfolio を使う因果戦略の富 `S*_n` が

- 条件付き成長率の増加極限 `W_∞ := lim_k W*(X_0 | X_{-1}, …, X_{-k})` に対し
- `(1/n) log S*_n → W_∞` a.s. (+ 望ましくは L¹)

を満たすことを headline とする (CT 16.5.1)。fixed-b 版 (`seqLogWealth_div_tendsto_stationary`) は親 Leg B が所有。

**Approach — finite-alphabet SMB は lift 不可、sandwich *構造* のみ再利用**。CT 16.5.1 の証明は SMB (§16.8) と
同じ **Algoet–Cover sandwich** — k 次 Markov 近似の富の block 平均が liminf/limsup で真の `W_∞` を挟み込む —
を採る。in-project SMB 機構はこの sandwich を実装済だが **有限アルファベット専用**:

- `shannon_mcmillan_breiman` (`SMB/AlgoetCover/Liminf.lean:497`) と `shannon_mcmillan_breiman_of_sandwich`
  (`SMB/McMillanBreiman.lean:88`) はいずれも `[Fintype α] [DecidableEq α]` 前提、`blockLogAvg` / `entropyRate`
  は **pmf ベースの block 確率**依存。連続 price-relative の general-measure 市場に **decl はそのまま lift 不可**。
- 一方 sandwich の **論理骨格** (Birkhoff を k 次条件付き量に適用 → 単調収束で 2 境界を close) は市場でも同型。

⟹ 本計画は「finite SMB decl を再利用」ではなく「sandwich *パターン*を real-valued log-wealth 用に再構築」する。
3 部品:

1. **R1 可測選択**: 各条件付き法 (無限過去 σ-代数で条件付け) について、simplex 上の凹成長率
   `growthRate` の最大点 `b*` を **可測に選ぶ**。凹性 (`growthRate_concaveOn`、親 Basic) + compact simplex 上の
   最大点存在 (`IsCompact.exists_isMaxOn`) は在庫。**核 = 条件付け (ω / 条件付き法) への可測依存** = 可測 argmax
   (Kuratowski–Ryll-Nardzewski / measurable selection)。ここが本 family 初の新規機構。
2. **R2 単調収束**: 条件付き成長率 `W*(X_0 | X_{-1..−k})` は k 増加で単調非減少 (条件付けを増やすと growth 増、
   data-processing 型) かつ上に有界 ⟹ 増加極限 `W_∞` に収束 (単調収束)。real-valued 条件付き期待
   (`condexp`、Mathlib `MeasureTheory.condExp`) で `W*(·|·)` を定義し、単調性を conditional Jensen / KT で得る。
3. **R3 real-valued AEP**: `(1/n) log S*_n = (1/n) ∑_i log(b*_i · X_i)` が `W_∞` に収束。sandwich —
   k 次近似の下界 (`birkhoff_ergodic_ae` を k 次条件付き log-return に適用 → `W*(X_0|past_k)`) と上界 (真の
   log-optimal ≤ 各 k 近似 + R2) で `W_∞` を挟む。`birkhoff_ergodic_ae` (`BirkhoffErgodic.lean`) は市場でも
   適用可 (親 Leg B fixed-b が実証)。

**着手順 (gateway-first)**: R1 (可測選択 = 最新規、gateway) → R2 (条件付き単調性) → R3 (sandwich) → R4 (組立)。
R1 の可測 argmax が通れば残りは Birkhoff + 単調収束の既存テンプレ再利用に落ちる。R3 は独立 gateway atom で
「real-valued sandwich が Birkhoff で閉じるか」を早期に壁判定 (finite SMB の Algoet–Cover 補題群のうち
alphabet 非依存な骨格がどれだけ救えるかを実機確認)。

## Phase 詳細

### M0 在庫 (proof-log: no)

- [ ] `MeasureTheory.condExp` の real-valued 条件付き期待 API + `Filtration` / tail σ-代数の in-project 使用例確認。
- [ ] measurable selection: `MeasurableSet.exists_measurable_...` / `IsCompact.exists_isMaxOn` /
      Kuratowski–Ryll-Nardzewski 系の Mathlib 在庫を verbatim 署名 (型クラス前提込み) で確定 (loogle)。
- [ ] `birkhoff_ergodic_ae` (`BirkhoffErgodic.lean`) + `AlgoetCover/` の sandwich 補題群のうち **alphabet 非依存**
      に切り出せる骨格を洗い出す (どの補題が `[Fintype α]` に本質依存かを機械確認)。
- [ ] 親 Leg B `stationaryLogReturn` / fixed-b headline の再利用面を確定。

### R1 — 条件付き log-optimal portfolio の可測選択 (proof-log: yes、gateway atom)

**目標 (sketch、実装で確定)**: 無限過去で条件付けた法 `ρ_ω` について、`b* : Ω → (Fin m → ℝ)` を可測に選び
`b* ω ∈ stdSimplex ℝ (Fin m)` かつ `growthRate ρ_ω X (b* ω)` を最大化する。凹性 + compact 最大点存在は在庫、
核は **可測依存**。gateway 判定: 可測 argmax が Mathlib 資産 (measurable selection) で閉じるか、self-build 要か。

### R2 — 条件付き成長率の単調収束 (proof-log: yes)

`W*(X_0 | X_{-1..−k})` を real-valued `condExp` で定義 → k 単調非減少 (条件付け増 ⟹ growth 増) + 上界
(無条件 `W*(X_0)` 以下でなく、`E[log ‖X_0‖]` 級の可積分性上界) ⟹ 単調収束で `W_∞`。single-letter 上界の
向き・可積分性前提を M0 honesty guard で実機確認 (coarse/fine ミスマッチ排除)。

### R3 — real-valued SMB 級 AEP (proof-log: yes、独立 gateway)

`(1/n) log S*_n → W_∞` を Algoet–Cover sandwich で。下界 = `birkhoff_ergodic_ae` を k 次条件付き log-return に
適用、上界 = 真の log-optimal 富 ≤ k 次近似富 + R2。**独立 gateway**: 「finite SMB の sandwich 骨格のうち
alphabet 非依存部を real-valued log-wealth に効かせられるか」を単独 atom で早期に壁判定。

### R4 — 組立 + 配線 + 独立監査 (proof-log: no)

R1–R3 を CT 16.5.1 headline に組み、root import 登録 / README / roadmap / facts / 独立 `honesty-auditor` +
`style-auditor`。headline を `@[entry_point]` + proof-done で `@audit:ok`。

## 壁リスク評価

- **R1 可測選択**: 中。凹最大点存在は在庫、可測 argmax が Mathlib measurable-selection で閉じれば軽い。
  閉じなければ self-build (Kuratowski–Ryll-Nardzewski 系の適用、~数十–150 行)。**loogle 0-hit だけで壁宣言せず**
  conclusion-shape 検索 + template lemma 自作行数見積を経由 (CLAUDE.md「壁を宣言するとき」)。
- **R2 単調収束**: 低〜中。`condExp` + 単調収束は Mathlib 在庫。条件付き KT / conditional Jensen の real-valued
  版が既存かで振れる。
- **R3 real-valued AEP**: **最リスク**。finite SMB decl は lift 不可 (機械確認済) ゆえ sandwich を real-valued で
  再構築。Algoet–Cover 骨格の alphabet 非依存部がどれだけ救えるかは M0 / gateway で確定するまで未知
  (`human-judgment`、low-trust)。genuine Mathlib gap を露呈したら新 wall slug を建てる。
- **総評**: real-valued SMB 級 AEP が本計画の重心。fixed-b (親 Leg B) が Birkhoff だけで閉じたのに対し、
  W_∞ は可測選択 + 単調収束 + sandwich の 3 段を要し格段に重い。

## 撤退ライン

- **R1/R2/R3 のいずれか**: 詰まった補題は signature を target 形のまま body を `sorry` +
  `@residual(plan:portfolio-stationary-woo-plan)` (slug = 本ファイル stem、整合)。**W_∞ / 可測選択 / 成長率極限を
  仮説で渡す load-bearing bundling は禁止** — retreat exit は `sorry` のみ。
- **R3 が genuine Mathlib gap (real-valued SMB) と確定した場合**: analytic core を `sorry` +
  新規 `@residual(wall:<name>)` で分離 (`docs/audit/audit-tags.md` register に追記)、組立骨格 (sandwich の
  上下界を仮定した consumer) は救う。**積分核 / AEP 極限を `*Hypothesis` predicate に抱えさせる形は禁止**。

## 正直性メモ (regularity precondition の性質)

追加仮説は **regularity precondition** に限る (load-bearing bundling 禁止):

- 定常エルゴード性 (`MeasurePreserving` / `Ergodic`) / 可積分性 (`Integrable (log ‖X_0‖)` 級) / 可測性:
  Birkhoff / condExp / 単調収束の必須前提、命題の核 (W_∞ 収束) を encode しない。
- simplex 帰属 / positivity (`0 < b·X`): 成長率解釈 + `Real.log` 定義域の correctness precondition。
- **`W_∞` の値そのもの・可測選択の存在・AEP 極限を仮説で渡す形は取らない** (それらは本計画が証明すべき核心)。

## DoD / gate

- **各 phase**: type-check done (`lake env lean` 0 error) で commit/push 可。proof-done (0 sorry ∧ 0 @residual、
  file 内) が genuine 完成。
- **headline `@[entry_point]`**: CT 16.5.1 完全形 headline を proof-done + 独立 `honesty-auditor` PASS で
  `@audit:ok`。
- **honesty gate**: 新規 `sorry` + `@residual` 導入 commit は独立 `honesty-auditor` 必須 (regularity precondition が
  load-bearing でない旨、可測選択/単調収束/AEP が仮説から semantic follow する旨も検査)。
- **style gate**: 新規 file の decl/docstring 追加で `style-auditor` を touched file に適用。

## 完了時の配線

- **root**: 新規 file (`Portfolio/StationaryWinfty.lean` 等、R4 で命名確定) の import を `InformationTheory.lean` に登録。
- **README / roadmap / facts**: `docs/readme-theorems.txt` Ch.16 節 / `docs/textbook-roadmap.md` Ch.16 行 /
  `docs/shannon/portfolio-facts.md` に headline の sorryAx-free 再検証コマンドを追記。
- **parent 同期**: 状態変化時は親 [`portfolio-operational-plan.md`](portfolio-operational-plan.md) の Leg B 完全形
  行を同期 (子が SoT、衝突時は親を子に合わせる)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)、active のみ残す。

1. **finite-alphabet SMB は lift 不可 (active)**: `shannon_mcmillan_breiman` / `shannon_mcmillan_breiman_of_sandwich`
   は `[Fintype α]` + pmf ベース `blockLogAvg` 依存を機械確認 (2026-07-19)。real-valued 市場では decl 再利用不可、
   Algoet–Cover sandwich の **論理骨格のみ**を再構築する方針。M0 で alphabet 非依存に救える補題を洗い出す。

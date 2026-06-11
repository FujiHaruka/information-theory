# AWGN achievability — 3 shared 壁 discharge + statement-fix サブ計画

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md) F-1 (achievability typicality)。
> **Sibling (history)**: [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md) (DONE、3 壁を staged/shared sorry 化した元 plan) / [`awgn-power-constraint-realizable-pivot-plan.md`](awgn-power-constraint-realizable-pivot-plan.md) (judgment #7 = 1 回目の power-constraint pivot)。
> **Facts ledger**: [`awgn-facts.md`](awgn-facts.md) (壁 overturn / 残存壁 / 確定事実の SoT)。

## 進捗

- [ ] M0 — 在庫確認 (n-dim diffEntropy / klDiv 積分解 / engine の再確認のみ。新規 inventory 不要) 📋
- [ ] Phase 1 — Wall 1 (i) joint mass: engine wiring 📋
- [ ] Phase 2 — Wall 1 (iii) indep-pair: klDiv 積分解 📋
- [ ] Phase 3 — Wall 1 (ii) statement-fix: `klDiv`-to-`volume` → joint `differentialEntropy` 形 📋
- [ ] Phase 4 — Wall 2 (random-coding union bound) 📋
- [ ] Phase 5 — Wall 3 statement-fix (expurgation 形) + consumer restructure 📋
- [ ] Phase V — verify + 親 plan / facts ledger 同期 + 独立 honesty 監査 📋

## ゴール / Approach

### Goal

`AWGN/Walls.lean` の achievability 側 3 shared sorry 補題 (`continuousAepGaussian_holds` /
`awgnRandomCodingBound_holds` / `awgnPowerConstraintHonest_holds`) を **genuine closure** し、
親 plan F-1 の headline `awgn_achievability_F1_via_staged_hyps` /
`awgn_theorem_F4_discharged_F1_via_staged` (`AchievabilityDischarge.lean`) を transitively
sorryAx-free にする。converse は既に genuine 完了済 (`awgn_converse`)。本 plan 完走で AWGN
channel coding theorem 全体 (achievability + converse) が genuine。

3 補題のうち 2 つ (Wall 1 (ii) / Wall 3) は **false statement** と判明済 (壁ではない、`@audit:retract-candidate(false-statement)`)。よって本 plan は純粋な discharge ではなく
**discharge + statement-fix の混合**。

### Approach (overall strategy / shape of solution)

3 壁の正体は本セッションで攻略済 (詳細 → [`awgn-facts.md`](awgn-facts.md) 残存壁テーブル + 各
docstring の STATUS/FINDING)。攻略 route を Phase 順に:

- **Wall 1 = 3 sub-bound の ∃A 形** (`continuousAepGaussian_holds`)。本 plan の中核。3 sub-bound
  を独立に処理する:
  - **(i) joint mass `≥ 1−ε`** = false-wall overturn 済 (engine genuine)。集中エンジン
    `pi_empirical_mean_concentration` / `pi_empirical_mean_typical_mass`
    (`AchievabilityAEP.lean`、sorryAx-free、abstract `μ` + L² 統計量 `φ`) に joint AWGN i.i.d.
    法則 + per-letter log-density `φ` を wiring。`MemLp φ 2` 確認 (Gaussian の有限モーメント)。
    無限積測度 SLLN 不要 (有限-`n` Chebyshev)。
  - **(iii) indep-pair bound** = sound (両 prob measure ゆえ真 MI `n·I(X;Y) ≥ 0`)。klDiv 積分解
    (`klDiv_pi_eq_sum` / `klDiv_prod_eq_add`) + engine + `ENNReal.toReal_nonneg` で攻略。
  - **(ii) volume bound** = **mis-stated**。現行 `klDiv (pi gaussian) volume` は無限参照 `volume`
    ゆえ `ν.real univ = 0` に退化し微分エントロピーを計算せず、`ofReal(−n·h−1) → 0` クランプ →
    (i) と両立不能 (machine 確認済)。**statement-fix 要**: 真の joint 微分エントロピー
    `jointDifferentialEntropyPi` 形に再 state。**重要**: 下流 consumer は (ii) を destructure
    時に `_hA_vol` で **discard** している (call site 確認、下記 blast radius)。よって (ii) の
    statement-fix は consumer の証明義務に波及しない (= 下流負債ゼロの def-fix)。
- **Wall 2 = union bound + Fubini** (`awgnRandomCodingBound_holds`)。abstract decoder 形。Wall 1
  の AEP に依存。union bound 自体は素直、analytic content は `gaussianCodebook` 上の Fubini +
  IndepFun + AEP-chain。
- **Wall 3 = power constraint** (`awgnPowerConstraintHonest_holds`)。**mis-stated**。`∀m`-over-`M=⌈exp(nR)⌉`
  形は独立積 `q^M`、`R > ψ(chi-sq LD rate)` で `→ 0`、capacity 近傍で `ψ ≪ R` ゆえ充足不能
  (machine refuted: `N=1,P=3,R=0.5 ⇒ ψ≈0.016 ≪ R`)。**statement-fix 要**: 標準 Cover-Thomas は
  power を **expurgation** で扱う (期待割合 `1−q → 0` の WLLN/Markov 事実のみ、指数 rate 不要)。
  expected-fraction 形 (`∫ codebook, …` shape、`awgnRandomCodingBound_holds` 類似) に置換 +
  consumer 側 expurgation で power-violator を取り込む。

**Phase 依存順** (engine → klDiv → statement-fix → Wall 2 → Wall 3 + consumer): (i) engine
wiring を最初に確立すると (iii)/(ii)/Wall 2/Wall 3 が同じ engine + klDiv 積分解パターンを再利用
できる。statement-fix 2 件 (Wall 1 (ii) / Wall 3) は signature を変えるため、consumer 波及を
明示的に管理する Phase に分ける (Phase 3 / Phase 5)。

**Mathlib-shape-driven の確定**: (ii) の再 state は既存 n-dim 資産 `jointDifferentialEntropyPi`
(`Draft/Shannon/MultivariateDiffEntropy.lean:77`) + subadditivity bridge
`jointDifferentialEntropyPi_le_sum` (:542) + per-coord `jointDifferentialEntropyPi_pi_eq_sum`
(`ParallelGaussian/Converse/Core.lean:145`) の **結論形に合わせて** 書く。これらは judgment #3
(2026-05-24) 時点では「n-d differentialEntropy 不在」と inventory が判断していたが、converse
closure 過程で導入済 (M0 で再確認済、下記 §M0)。

## 既存資産インベントリ (M0 で再確認、file:line)

新規 inventory は不要。本 plan が依拠する現存資産:

| 資産 | file:line | 用途 | sorryAx 状態 |
|---|---|---|---|
| `pi_empirical_mean_concentration` | `AWGN/AchievabilityAEP.lean:38` | (i) engine: 有限-n Chebyshev 集中 (abstract μ+φ) | sorryAx-free (facts ledger) |
| `pi_empirical_mean_typical_mass` | `AWGN/AchievabilityAEP.lean:130` | (i) engine: ∃N₀ で mass `≥ 1−η` の存在形 | sorryAx-free |
| `jointDifferentialEntropyPi` (def) | `Draft/Shannon/MultivariateDiffEntropy.lean:77` | (ii) statement-fix の再 state 先 (`-∫ negMulLog (rnDeriv vol)`) | def (genuine shape) |
| `jointDifferentialEntropyPi_le_sum` | `Draft/Shannon/MultivariateDiffEntropy.lean:542` | n-dim subadditivity `h(Yⁿ) ≤ ∑ h(Yᵢ)` (genuine) | `@audit:ok` |
| `klDiv_pi_marginals_toReal_eq_sum_sub_joint` | `Draft/Shannon/MultivariateDiffEntropy.lean:467` | n-dim KL ↔ entropy 差 bridge | `@audit:ok` |
| `jointDifferentialEntropyPi_pi_eq_sum` | `ParallelGaussian/Converse/Core.lean:145` | i.i.d. `Measure.pi` の joint entropy = `n · h₁` | (M0 で sorryAx 確認) |
| `klDiv_pi_eq_sum` | `Shannon/MIChainRule.lean:249` | (iii): `klDiv (pi P) (pi Q) = ∑ klDiv P Q` | (M0 で確認) |
| `klDiv_prod_eq_add` | `Shannon/MIChainRule.lean:230` | (iii): prod の KL 加法分解 | (M0 で確認) |
| `klDiv_gaussianReal_gaussianReal_eq` | `Shannon/DifferentialEntropy.lean:672` | 1-D Gaussian KL closed form | (既存) |
| `awgn_expurgate_worst_half` | `AWGN/AchievabilityDischarge.lean:526` | Wall 3: 既存 worst-half throwaway (`∑ Pe ≤ M·2ε ⇒ M/2 個が `≤ 4ε`) | `@audit:ok` |
| `awgn_exists_codebook_le_avg` | `AWGN/AchievabilityDischarge.lean:509` | codebook-average → ∃ codebook 抽出 | (既存) |
| `awgnPowerWitness_exists` | `AWGN/AchievabilityDischarge.lean:614` | strict slack `P' < P` witness | `@audit:ok` |

**M0 で確定すべき numeric/型予測** (verbatim 確認義務、CLAUDE.md):

- `jointDifferentialEntropyPi_pi_eq_sum` の結論形 (i.i.d. で `n · differentialEntropy P` か、
  `∑ᵢ differentialEntropy (μ i)` か) を Read で verbatim 確認 → (ii) の再 state 右辺を確定。
- `klDiv_pi_eq_sum` / `klDiv_prod_eq_add` の `[...]` 型クラス前提 (prob measure / SigmaFinite)
  を verbatim 確認 → engine の `IsProbabilityMeasure` 維持要件と突合。
- (i) の `φ` = per-letter log-density に対する `MemLp φ 2 μ` が Gaussian で成立すること
  (log-density は二次多項式オーダー、Gaussian の有限高次モーメントで `MemLp 2`) を退化境界
  (`P=0` / `N=0`) で生き残るか確認。

## consumer restructure の影響範囲 (blast radius、`scripts/dep_consumers.sh` 実測)

3 壁すべて consumer は **`AchievabilityDischarge.lean` 1 file のみ**。`--transitive` で full blast
radius も 1 file 内 3 decl:

| 壁 | direct consumers | transitive closure |
|---|---|---|
| `continuousAepGaussian_holds` | 2 decl (`awgn_avg_error_union_bound:446` / `isAwgnTypicalityHypothesis:716`) | — |
| `awgnRandomCodingBound_holds` | 2 decl (同上) | — |
| `awgnPowerConstraintHonest_holds` | 1 decl (`isAwgnTypicalityHypothesis:716`) | 3 decl (`:716` → `awgn_achievability_F1_via_staged_hyps:1397` → `awgn_theorem_F4_discharged_F1_via_staged:1425`) |

いずれも `InformationTheory/Shannon/AWGN/AchievabilityDischarge.lean` 内に閉じる (他 family /
lineage への波及なし)。

**重要な consumer 構造所見** (statement-fix の波及を de-risk):

1. **Wall 1 (ii)/(iii) は consumer で discard 済**。call site (`AchievabilityDischarge.lean:486` +
   `:934`) は AEP を `obtain ⟨A, hA_meas, _hA_prob, _hA_vol, _hA_indep⟩` で destructure し、
   **`_hA_vol` (ii) と `_hA_indep` (iii) を `_` で捨てている**。consumer が実消費するのは
   `hA_meas` (可測性) と (i) mass のみ。error-prob bound は Wall 2 経由で流れる。
   → **(ii) statement-fix は consumer 証明義務に波及しない** (signature を `jointDifferentialEntropyPi`
   形に変えても consumer の `_hA_vol` discard はそのまま通る)。
2. **Wall 3 の `∀m`-mass は consumer で barrier-integrand に畳まれる**。
   `AchievabilityDischarge.lean:948-1000` 付近で power-OK mass を
   `g c := ∑_m Pe c m + M · 𝟙_{¬power}(c)` の barrier 項に組み込み、`∫⁻ g ≤ M·2·ε_d2` を経由して
   `awgn_exists_codebook_le_avg` + `awgn_expurgate_worst_half` に渡す。つまり consumer は既に
   **expurgation-style averaging** で power-violator を penalty 化している。expected-fraction 形
   への statement-fix はこの barrier 項にそのまま接続する (mass 形より自然)。
   → Wall 3 の statement-fix は **consumer の barrier 構造を expected-fraction に合わせて再配線**
   する Phase 5 で `isAwgnTypicalityHypothesis` (716) の body を touch する。`:1397` / `:1425`
   wrapper は signature 不変なら自動追従 (1 行 pass-through)。

**工数感**: statement-fix 2 件は signature 変更を伴うが blast radius が 1 file 3 decl に限定 +
(ii) は consumer discard 済ゆえ実 touch は Phase 5 (Wall 3) の `isAwgnTypicalityHypothesis` body
restructure が主。

## Phase 詳細

### M0 — 在庫再確認 (proof-log: no)

- [ ] §既存資産インベントリの 11 資産の file:line を Read で verbatim 確認 (signature + `[...]` 型クラス前提 + 結論形)
- [ ] M0 numeric/型予測 3 件 (`jointDifferentialEntropyPi_pi_eq_sum` 結論形 / klDiv 型クラス前提 / `MemLp φ 2` の退化境界生存) を verbatim 確認
- [ ] `#print axioms` で `jointDifferentialEntropyPi_pi_eq_sum` / `klDiv_pi_eq_sum` の sorryAx 状態を確認 (依拠先が genuine か)
- 撤退ライン: なし (在庫確認のみ)

### Phase 1 — Wall 1 (i) joint mass: engine wiring (proof-log: yes)

- [ ] joint AWGN i.i.d. 法則 (`(pi N(0,P)).prod (pi N(0,N)) |> map (X, X+Z)`) を engine の
      abstract `μ` (per-letter joint `(x, x+z)` の法則) に instantiate
- [ ] per-letter log-density を `φ` に substitute、`MemLp φ 2` を Gaussian 有限モーメントで証明
- [ ] `pi_empirical_mean_typical_mass` から `∃ N₀, mass ≥ 1−ε` を取り出し (i) の conjunct に接続
- 撤退ライン: `MemLp φ 2` が log-density で詰まる場合、(i) のみ
      `sorry + @residual(plan:awgn-achievability-walls-discharge)` を残置 (engine は genuine、
      wiring の integrability が残課題)。**(i) を `*Hypothesis` に bundle しない** (engine は
      regularity 前提のみ取る abstract 形を維持)。

### Phase 2 — Wall 1 (iii) indep-pair: klDiv 積分解 (proof-log: yes)

- [ ] `klDiv_pi_eq_sum` で n-dim KL を `∑ᵢ klDiv (per-letter joint) (per-letter prod)` に分解
- [ ] `klDiv_prod_eq_add` + `klDiv_gaussianReal_gaussianReal_eq` で per-letter MI を closed form 化
- [ ] engine + `ENNReal.toReal_nonneg` で `n · I(X;Y) ≥ 0` 系の AEP indep-pair upper bound を導出
- 撤退ライン: per-letter MI の closed form が詰まる場合、(iii) のみ shared sorry 残置
      `@residual(plan:awgn-achievability-walls-discharge)`。bundle 禁止。

### Phase 3 — Wall 1 (ii) statement-fix (proof-log: yes)

- [ ] `continuousAepGaussian_holds` の (ii) conjunct を `klDiv (pi gaussian) volume` 形から
      `jointDifferentialEntropyPi` (真の joint 微分エントロピー) 形に再 state
- [ ] `jointDifferentialEntropyPi_pi_eq_sum` (i.i.d. → `n · h₁`) + `differentialEntropy_gaussianReal`
      で右辺を closed form `volume A ≤ exp(n·(h(P+N)+ε))` 形に整える (退化バグ解消)
- [ ] 再 state 後の (ii) を engine + subadditivity bridge で genuine 証明 (or 残課題なら shared sorry)
- [ ] **consumer 確認**: `:486` / `:934` の `_hA_vol` discard が新 signature で通ることを `lake env lean`
      で確認 (signature 変更が consumer 証明義務に波及しないことを機械検証)
- 撤退ライン: 再 state は完了させる (false-statement の解消が本 Phase の必須成果)。証明本体が
      詰まる場合は新 signature の body を `sorry + @residual(plan:awgn-achievability-walls-discharge)`
      で残置 — ただし **signature は honest な `jointDifferentialEntropyPi` 形** (false statement を
      残さない)。`@audit:retract-candidate(false-statement)` は statement-fix 完了で外す。

### Phase 4 — Wall 2 (random-coding union bound) (proof-log: yes)

- [ ] abstract decoder 形 `awgnRandomCodingBound_holds` の `∫⁻ codebook, (pi awgnChannel) {y | decoder ≠ m} ≤ 2ε` を
      union bound + Fubini で展開
- [ ] `gaussianCodebook` 上の IndepFun (`iIndepFun_pi`) + Wall 1 (i) の AEP mass (Phase 1 成果) を
      AEP-chain に接続
- 撤退ライン: AEP-chain の measurability/Fubini が詰まる場合、shared sorry 残置
      `@residual(plan:awgn-achievability-walls-discharge)`。decoder は abstract parameter のまま
      (consumer が `jointTypicalDecoder` を inject、bundle 化しない)。

### Phase 5 — Wall 3 statement-fix (expurgation 形) + consumer restructure (proof-log: yes)

- [ ] `awgnPowerConstraintHonest_holds` を `∀m`-mass 形から **expected-fraction** 形に再 state:
      codebook-average で power-violator の期待割合 `→ 0` (per-codeword `1−q → 0`、WLLN/Markov、
      指数 rate 不要)。`awgnRandomCodingBound_holds` の `∫ codebook, …` shape を雛形に
- [ ] 再 state 後の expected-fraction bound を engine (Phase 1 の chi-square 集中) + Markov 不等式で
      genuine 証明
- [ ] **consumer restructure** (`isAwgnTypicalityHypothesis:716` body): barrier-integrand
      `g c := ∑_m Pe c m + M · 𝟙_{¬power}(c)` (`:948-1000`) の power 項を expected-fraction 形に
      合わせて再配線。`awgn_expurgate_worst_half` (`:526`) + `awgn_exists_codebook_le_avg` (`:509`)
      の throwaway に接続
- [ ] `awgn_achievability_F1_via_staged_hyps:1397` / `awgn_theorem_F4_discharged_F1_via_staged:1425`
      が signature 不変で自動追従することを確認 (pass-through 1 行)
- 撤退ライン: expected-fraction 再 state は完了させる (false-statement 解消が必須)。consumer
      restructure が詰まる場合、shared 補題は新 signature で genuine、consumer body のみ
      `sorry + @residual(plan:awgn-achievability-walls-discharge)`。**`∀m`-mass false statement を
      残さない**。`@audit:retract-candidate(false-statement)` は statement-fix 完了で外す。

### Phase V — verify + 同期 + 監査 (proof-log: no)

- [ ] `lake env lean InformationTheory/Shannon/AWGN/Walls.lean` + `AchievabilityDischarge.lean` silent
- [ ] `#print axioms` で `awgn_achievability_F1_via_staged_hyps` / `awgn_theorem_F4_discharged_F1_via_staged`
      が sorryAx-free (= `[propext, Classical.choice, Quot.sound]`) を確認
- [ ] 親 `awgn-moonshot-plan.md` の進捗ブロック (Phase B / F-1 撤退ライン) + facts ledger 残存壁
      テーブルを更新 (3 壁 → genuine、statement-fix 2 件の経緯を 1 行ずつ)。**親子 co-stage** (pre-commit WARN)
- [ ] 独立 honesty 監査 (`honesty-auditor`): statement-fix 2 件の新 signature が honest
      (false statement 解消 + load-bearing bundle なし) + `@residual` 分類正当性 + consumer
      restructure の sufficiency を検査

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。決着済 entry は削除 (git が履歴)。

### #1 (起草) statement-fix 2 件は consumer 波及が限定的

`scripts/dep_consumers.sh` 実測で 3 壁の blast radius は `AchievabilityDischarge.lean` 1 file 内。
Wall 1 (ii) は consumer が `_hA_vol` で **discard** 済 (`:486` / `:934`) ゆえ statement-fix が
証明義務に波及しない。Wall 3 は consumer の barrier-integrand (`:948`) が既に expurgation-style
averaging を行っているため、expected-fraction 形への statement-fix が mass 形より自然に接続する。
よって 2 件の statement-fix は signature 変更を伴うが、実 touch は Phase 5 の
`isAwgnTypicalityHypothesis` body restructure が主。

### #2 (起草) judgment #3 / #7 の盲点を継承しない

judgment #3 (typicality plan、`klDiv` 形採用) は (ii) を `klDiv`-to-`volume` で書いたが、無限参照
`volume` の `ν.real univ = 0` 退化を見落とした (false statement)。judgment #7 (power-constraint
realizable pivot) は `P_cb < P_target` slack で `P_cb = P_target` 退化のみ patch し、
`∀m`-over-`exp(nR)` の指数 rate 障害を見落とした (false statement)。本 plan の statement-fix は
両盲点を解消する形 ((ii) = 真の `jointDifferentialEntropyPi` / Wall 3 = expected-fraction
expurgation) を採り、honest signature に置換する。

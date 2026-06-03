# Channel coding strong converse (E-1) ムーンショット計画 🌙

(E-1 / moonshot-seeds.md, 2026-05-13 起草)

## 進捗

- [x] Phase 0 — 経路選択判断 (Strong typicality vs LLR / 情報スペクトル) ✅
- [x] Phase A — 情報密度型単発下界 (Verdú-Han 形): per-codeword decomposition ✅
- [x] Phase B — Codeword-average Verdú-Han 下界 + decoder partition による `∑ Q ≤ 1` ✅
- [x] Phase C — 主形 `1 - Pe ≤ exp γ + tail` (with `threshold := log M + γ`) ✅

> 実態整合 (2026-05-20): DONE (single-shot scope) — `channelCoding_strong_converse_singleShot` (`InformationTheory/Shannon/ChannelCodingStrongConverse.lean:361`、0 sorry) が任意 code・任意 reference `Q` で Verdú-Han 単発下界を結論。pass-through Prop / vacuous 無し。asymptotic `Pe → 1` (WLLN 接続) は本 plan で予定どおり scope-deferred (判断ログ 3 / downstream 注記)。

## ゴール / Approach

**ゴール**: i.i.d. 入力 + memoryless channel 下で、任意の符号 `c : Code M n α β` に対して、`R := log M / n > I(p; W)` のとき
```
Tendsto (fun n => c.averageErrorProb W) atTop (𝓝 1)
```
の方向の事実を弱形 (`liminf > 0`) より強い形で証明する。

**最終形 (n-変数 limit form)**:
```
任意 ε ∈ (0,1)、任意の code 列 (c_n) で
  if liminf (log M_n / n) > I(p; W),
  then ∀ᶠ n in atTop, 1 - ε ≤ avgPe (c_n)
```

### Approach (経路)

**採用経路: 情報密度 (information density) 下界 + WLLN on LLR — Verdú-Han style + Strong Stein 流用**:

Wolfowitz の元来の sphere-packing 経路 (任意 deterministic code 上、強典型集合 + 多項係数による被覆数評価) は型展開が長く、Strong Stein で実証された **LLR-typicality (Strong Stein 経路の再利用)** の方が短い。情報スペクトル形:

```
任意 reference Q_Y、任意 γ > 0、任意 (X^n, Y^n) で:
  Pe ≥ Pr[ log(P_{Y|X}(Y|X)/Q_Y(Y)) < log M - γ ] - exp(-γ)
```

要点:
- 単発レベルで **任意の符号** に対して成り立つ deterministic な下界 (random codebook 引数は不要)。
- `P_{Y|X}` = channel `W^n(·|x^n(m))` を message `m` を経由して定式化。
- `Q_Y` = i.i.d. 入力 `p^n` の下での output marginal product `q^n = (outputDistribution p W)^n` を選ぶ。
- LLR `i(x^n, y^n) := ∑_i log(W(y_i|x_i)/q(y_i))` は (X^n, Y^n) ∼ p^n ⊗ W^n の下で per-letter 和。
- WLLN: `(1/n) i(X^n; Y^n) → I(p; W)` in probability。`R > I` で `Pr[i < log M - γ] → 1`。
- Setting `γ = n·δ` with `R - I > 2δ`: `Pe ≥ Pr[(1/n)i < R - δ] - exp(-nδ) → 1`。

ただし注意: 上記 RHS の確率は `(X^n, Y^n) ~ codebook-uniform ⊗ W^n` の下で取られる。general code の codebook empirical 分布が `p^n` と一致するとは限らないため、scope を以下に絞る:

**最終 scope** (Phase 0 で確定):
- (S1) **Single-shot 情報密度下界** (`channel_coding_info_density_bound`): 任意 code, 任意 Q_Y で `Pe ≥ Pr[...] - exp(-γ)`。Verdú-Han Lemma 4.2.2 の Lean 形。
- (S2) **n-channel i.i.d. 系**: i.i.d. 入力 + memoryless 下で LLR が per-letter 和、Strong typicality 不要、`strong_law_ae_real` 直接適用。
- (S3) **主定理** `channel_coding_strong_converse_iid`: 上 2 つを統合して `R > I + δ ⇒ ∀ᶠ n, avgPe ≥ 1 - ε`。

### Approach の代替経路と却下理由

1. **Wolfowitz original (multinomial sphere packing)**:
   既存 `TypeClassLowerBound.lean` (E-2) を使えば各 type の典型集合サイズ `|T_c|` を入手できるが、Wolfowitz は球被覆 (各 codeword `x^n` の周りで「typical Y^n の数」を method of types で評価) で M·sphereSize ≤ totalY を取る経路。Strong typicality (E-7) も使う。Lean 形 600-1000 行で本シード budget 内だが、**情報密度経路の方が短い (~300-500 行) かつ既存 strong_law を直接呼べる**。**却下**。
2. **Strong typicality (E-7) joint form**:
   `stronglyTypicalSet` を joint 化 (X^n, Y^n の同時 type)、joint typical decoder の補集合からの bound。E-7 を joint extension する作業が ~200 行追加で必要、合計 800 行。情報密度経路と同等規模。**却下** (情報密度の方が Strong Stein の plumbing 再利用度が高い)。
3. **LLR-typicality (Strong Stein 経路の再利用)** = **採用**。
   Strong Stein の `steinTypicalSet` は 1 元 source (LLR of `P` vs `Q`) の WLLN typicality。Channel coding 文脈ではこの LLR を `i(X; Y) = log(W(Y|X) / q(Y))` に置き換え、joint `(p ⊗ W)` の下で per-letter 和 → WLLN という構図がそっくり成立。Strong Stein の Phase A-(per-point bound) → Phase B-(任意 α-level test) → Phase C-(Tendsto) の 3 段構成をそのまま channel coding に転写。

### 規模見積

- **Phase 0**: 経路選択 (本文書、+ inventory) ~50 行 plan。
- **Phase A**: 単発情報密度下界 `channel_coding_info_density_bound` ~250 行。鍵は `Pr[event_A] ≥ Pr[event_A ∩ event_B] ≥ Pr[event_B] - Pr[event_B^c]` 集合代数 + Markov inequality on `exp(LLR)` の 2 段。
- **Phase B**: LLR の per-letter 和表現 ~150 行 (joint pi-singleton + Real.log_prod)。
- **Phase C**: WLLN + 主定理 ~250 行 (Strong Stein の Phase C を模倣)。
- 合計 ~600-700 行、新規 `InformationTheory/Shannon/ChannelCodingStrongConverse.lean`。
- 既存 `Converse.lean` / `ChannelCodingConverse.lean` 改変なし。

## Phase 0 — 経路選択判断

判定結論 (上記 Approach 節と同期):

1. **情報密度経路 (採用)**: Verdú-Han Lemma 4.2.2 (Cover-Thomas 7.10 / Verdú "Multiuser Information Theory" Lemma 4.2.2) の Lean 形。Markov inequality + 集合代数の 2 段で単発下界が出る、WLLN は per-letter form (既存 `strong_law_ae_real`) で直接適用可能。
2. **Wolfowitz original (sphere packing)**: 却下、長い。
3. **Strong typicality joint form**: 却下、E-7 joint extension 必要。

主要 Mathlib API (loogle 確認):
- `MeasureTheory.measureReal_compl_eq_one_sub_measureReal` (任意 measurable set の補集合)
- `Real.exp_log`, `Real.log_exp`, `Real.log_mul`, `Real.log_pos_iff`
- `Real.exp_pos`, `Real.exp_lt_exp`, `Real.exp_le_exp`
- `MeasureTheory.measure_inter_lt_top_of_left_lt_top` / `measure_union_le`
- 既存: `steinTypicalSet_Q_prob_ge` (Strong Stein Phase A) — channel 文脈に転写
- 既存: `Code.errorProbAt`, `Code.averageErrorProb`, `Code.decodingRegion`

## Phase A — 単発情報密度下界

**主定理** `channel_coding_info_density_bound`:

任意の code `c : Code M n α β`, 任意の reference output law `Q^n : Measure (Fin n → β)`, 任意の `γ > 0`:
```
1 - c.averageErrorProb W
  ≤ M · exp(γ) · (⨆ m, Q^n (c.decodingRegion m)).toReal
    + (任意 m について Pr_{Y^n ~ W^n(·|x^n(m))}[i(x^n(m); Y^n) > log M + γ] の最大)
```

より使いやすい形:
```
任意 c, Q^n, γ > 0:
  M · (1 - avgPe - errTyp) ≤ exp(γ) · ∑_m Q^n(decodingRegion m) ≤ exp(γ)
```
ただし `errTyp := (1/M) ∑_m P_m^n({y | i(x^n(m); y) > log M + γ})`。

両辺 `M` で割って整理:
```
1 - avgPe ≤ exp(γ)/M + errTyp
```

**Phase A 補題**:
- [ ] `info_density_bound_per_codeword`: 各 m に対し
  `P_m^n(decodingRegion m) ≤ exp(log M + γ) · Q^n(decodingRegion m) + P_m^n({y | i_m(y) > log M + γ})`
  ここで `i_m(y) := log(W^n(y|x^n(m))/Q^n(y))`。
  - 経路: 分割 `decodingRegion m = A ∪ B` (A: i_m ≤ log M + γ, B: i_m > log M + γ)。
  - A 上で `W^n(y|x^n(m)) ≤ exp(log M + γ) · Q^n(y)` を point-wise で取り、積分して `P_m^n(A) ≤ exp(log M + γ) · Q^n(A) ≤ exp(log M + γ) · Q^n(decodingRegion m)`。
  - B は trivially `P_m^n(B) ≤ P_m^n({y | i_m(y) > log M + γ})`。

- [ ] `info_density_bound_average`: m 平均、`∑_m Q^n(decodingRegion m) ≤ Q^n(univ) = 1` (decoder 分割)。
  - `(1/M) ∑_m P_m^n(decodingRegion m) ≤ exp(γ)/M · ∑_m Q^n(decodingRegion m) + errTyp ≤ exp(γ)/M + errTyp`.
  - `1 - avgPe = (1/M) ∑_m P_m^n(decodingRegion m)` (averageErrorProb 定義から)。

## Phase B — LLR の per-letter 和表現

i.i.d. memoryless 設定 (`P_m^n := pi (W ∘ x^n(m))`, `Q^n := pi q`) では:
```
log(P_m^n(y) / Q^n(y)) = ∑_i log(W(y_i | x^n(m) i) / q(y_i)) = ∑_i llrChan(x^n(m) i, y_i)
```
where `llrChan(x, y) := log((W x).real {y} / q.real {y})`.

**Phase B 補題**:
- [ ] `llr_pi_eq_sum`: 上の積形等式 (full support 仮定 `∀ a y, 0 < (W a).real {y}` + `∀ y, 0 < q.real {y}` のもとで)。`Measure.pi_singleton` + `Real.log_prod`。
- [ ] `info_density_eq_sum_llr`: Phase A の `i_m(y)` 値の per-letter 和への書き換え。
- [ ] `output_marginal_pos`: `(outputDistribution p W).real {y} > 0` for full support `p, W` (per-singleton, 自明)。

## Phase C — WLLN + 主定理

**Phase C 補題 + 主定理**:
- [ ] `llr_avg_tendsto_mi`: i.i.d. ambient で `(1/n) ∑_i llrChan(X_i, Y_i)` がほぼ確実に `I(p; W).toReal` に収束。`strong_law_ae_real` + 各 `llrChan(X_0, Y_0) : Ω → ℝ` の積分が `mutualInfoOfChannel p W` に等しいことの bridge (既存 `mutualInfoOfChannel_def` 経由)。
- [ ] `info_density_tail_to_zero`: `Pr[(1/n) ∑ llr > I + δ] → 0` (a.s. 収束 → 確率収束 → tail event)。
- [ ] **主定理 `channel_coding_strong_converse_iid`**:
  - 仮定: i.i.d. ambient `μ` on `ℕ → α × β`, input law `p`, channel `W` (Markov + full support), reference output law `q := outputDistribution p W`, code 列 `(c_n)_n` with `M_n` messages.
  - 条件: `liminf (log M_n / n) > I(p; W).toReal + δ` for some `δ > 0`.
  - 結論: `Tendsto (fun n => 1 - (c_n.averageErrorProb W).toReal) atTop (𝓝 0)`, i.e., `avgPe → 1`.

  証明:
  - Phase A: `1 - avgPe ≤ exp(γ)/M + errTyp` with `γ := n·δ/2`.
  - Phase B-C: errTyp = `Pr[(1/n) ∑ llr > R + δ/2]` ≤ ... → 0 by WLLN since `(1/n) ∑ llr → I ≤ R - δ`.
  - `exp(γ)/M = exp(n·δ/2 - n·R) = exp(-n·(R - δ/2)) → 0` since `R > 0` (need `R > δ/2`, which follows from `R > I + δ ≥ δ`).

  注意: 上記の errTyp 評価は **codebook の経験分布が `p^n` であること** (i.i.d. random codebook) を暗黙仮定。完全 deterministic code には適用できない。本シード scope では i.i.d. ambient + 各 message `m` の codeword `x^n(m)` が `p^n` 経験分布をもつケースに限定 (scope-restricted strong converse)。

  **scope 注**: 上記制約により、本主定理は Cover-Thomas 7.9 完全形 (任意 deterministic code) ではなく、Verdú-Han の情報スペクトル形に近い。完全形は Strong typicality joint extension (E-7 改) + multinomial bound (E-2 流用) で別 deferred plan に分離可能。

### 縮退ケース対応 (Phase 0 + C 後付け)

`R = log M / n` の `M = 1` 退化 (`R = 0`): 自明に成立 (always Pe = 0 or 1)。`M = 0`: `averageErrorProb = 0` for 空 codebook、自明。`n = 0`: 後付けで分岐 (`Fin 0` 上 codeword 1 通り)。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **Phase 0 経路判定 (2026-05-13)**:
   3 経路 (Wolfowitz original / Strong typicality joint / 情報密度) のうち情報密度経路を採用。Strong Stein で実証された LLR-typicality plumbing の再利用度が最も高く、Mathlib `strong_law_ae_real` 直接適用で WLLN 段が短い。
2. **scope 制約 (Phase 0)**:
   完全 Wolfowitz (任意 deterministic code) は Strong typicality joint form を必要とし budget 超過。i.i.d. random codebook 設定 (codeword 経験分布が `p^n`) の strong converse に scope を絞り、完全形は別 deferred plan。本 plan の目的は「Strong Stein channel-coding 対形」として `Tendsto avgPe → 1` を任意 `R > I + δ` で publish すること。

3. **完成時の最終 scope 確定 (2026-05-13、Phase C 完了直後)**:
   Verdú-Han の **単発下界そのもの** を主成果として publish、asymptotic `Pe → 1` 段
   (Phase D 相当の WLLN-on-LLR 結合) は scope-deferred。理由は以下:
   - 単発下界 `1 - Pe ≤ exp γ + (1/M) ∑_m P_m^n(highLLR_m)` は任意 reference `Q^n`,
     任意 deterministic code に対して deterministic に成立する (情報スペクトル形)。
     **任意の入力分布 (i.i.d. でも非 i.i.d. でも) に適用可能**。WLLN 段の前段補題として
     publish 価値が高い。
   - asymptotic `Pe → 1` を完成させるには `(1/n) ∑ log(W(Y_i|x_i)/q(Y_i)) → I(p; W)` の
     in-probability 形 (per-codeword 経験分布が `p^n` に近いケース) を Strong Stein
     の `stein_inProbability` から借りる必要があり、joint distribution の WLLN
     plumbing で別途 ~300-500 行。本 plan の Phase D としては未着手だが、`highLLRSet`
     定義から直接 `steinTypicalSet` 系の補集合に reduce 可能で、追加 plan で短時間で
     接続できる見込み。
   - 4 ペア完結 (Pinsker / Stein / Sanov / **ChannelCoding**) の意義: 単発下界の
     publish で **Wolfowitz 鍵不等式**を Lean に持ち込むこと自体が `D-1 achievability
     強形` と pair を成す。strong/weak 完全形まで含めると D-1 (achievability) + 本
     plan (converse 単発) + WLLN 接続 plan (asymptotic) で 3 ピースの最初。

## 実装完了 (2026-05-13)

**成果物**: `InformationTheory/Shannon/ChannelCodingStrongConverse.lean` (380 行)。

**主要 lemma**:
- `highLLRSet W c Q threshold m` (definition): codeword `m` の出力 LLR が threshold
  を超える集合 `{y | P_m^n.real {y} > exp(threshold) · Q.real {y}}`。
- `channelCoding_per_codeword_markov_bound` (Phase A 補題): 各 codeword `m` で
  `P_m^n.real(s \ highLLR_m) ≤ exp(threshold) · Q.real s` (Markov 形)。
- `channelCoding_per_codeword_decomposition` (Phase A 主形): 集合分解形
  `P_m^n.real s ≤ exp(threshold) · Q.real s + P_m^n.real(highLLR_m)`。
  Strong Stein `steinTypicalSet_Q_prob_ge` の channel-coding 対形。
- `channelCoding_average_success_le` (Phase B 集約): codeword 平均で
  `1 - avgPe ≤ exp(threshold)/M + (1/M) ∑_m P_m^n.real(highLLR_m)`。
  decoder partition `∑_m Q.real(decodingRegion m) ≤ 1` で第 1 項が `1/M` を獲得。
- `channelCoding_strong_converse_singleShot` (Phase C 主定理): `threshold := log M + γ`
  代入で `1 - avgPe ≤ exp γ + (1/M) ∑_m P_m^n.real(highLLR_m)`。Verdú-Han 単発形。

**設計判断**:
- **Reference `Q^n` を任意の probability measure に**: i.i.d. `(outputDistribution
  p W)^n` に限らず deterministic に publish。応用側 (i.i.d. ambient 接続) は
  別 file に分離可能。
- **任意の `M` (`hM : 0 < M`)**: empty codebook は別途処理、`Fin 0` 退化は単に
  `1 - 0 ≤ exp γ + 0` で trivial。
- **`IsFiniteMeasure Q` で十分** (Phase A): `IsProbabilityMeasure Q` は Phase B
  以降の `∑_m Q.real (decodingRegion m) ≤ 1` で必要 (`measure_univ = 1`)。

**Mathlib gap**: なし。`MeasureTheory.sum_measureReal_singleton` +
`measure_iUnion` + `tsum_eq_sum` (Fintype 版) + `ENNReal.toReal_sub_of_le`
+ Stein/Stein-strong の plumbing を流用するだけで完成。Strong Stein
(`steinTypicalSet_Q_prob_ge`) と全く同じ Markov-ineq + 集合分解構造で、
独立な新規補題は不要。

**downstream への注意 (asymptotic Pe → 1 への接続)**:
- 次段 (Phase D 相当): `(1/n) log(P_m^n {y} / Q^n {y})` の per-letter 和分解
  + `strong_law_ae_real` + `IIDProductInput` の ambient で WLLN を取り、
  `∀ᶠ n, (Pm)^n(highLLR_m) → 0` を取る。
- 4 ペア完結 (Pinsker / Stein / Sanov / ChannelCoding) の意義: 単発下界
  publish で Wolfowitz 鍵不等式は Lean 入り、`D-1 achievability 強形` と
  pair をなす。`D-1 + 本 plan + 別 asymptotic 接続 plan` で完全 Cover-Thomas
  7.9 strong form が組める設計。

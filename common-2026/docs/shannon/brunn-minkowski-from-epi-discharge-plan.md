# Brunn-Minkowski (entropy form) `from EPI` discharge 計画 🌙

> **Parent**: [`brunn-minkowski-moonshot-plan.md`](brunn-minkowski-moonshot-plan.md) §残① / "撤退ラインの discharge 想定 L-BM1"
>
> 親 moonshot は **hypothesis pass-through で publish 済**
> (`brunn_minkowski_entropy_inequality` `BrunnMinkowski.lean:188` の本体は
> `IsBrunnMinkowskiEntropyHypothesis` (`:132`、= BM 結論そのもの) を受け取り
> `:= h_bm_entropy_assumed` `:197` で着地、honesty audit 上は **type ≡ conclusion**
> の典型 defect (`h_bm_entropy_assumed : IsBrunnMinkowskiEntropyHypothesis n h X Y P`
> は def-unfold で結論と defeq)。docstring 自認: 「結論を直接 hypothesis 化」「本体は
> `:= h_bm` の 1 行で着地」。
>
> 本 plan は **EPI 経由 (Cover-Thomas Theorem 17.7.4 / 17.9.2 同等性経由)** で
> L-BM1 を genuine discharge する route を起草する。**実装はまだ無い**。
>
> **scope 区別 (重要)** — sibling plan
> [`brunn-minkowski-closure-plan.md`](brunn-minkowski-closure-plan.md) は
> **Fubini 帰納直接路** (1D PL → n-dim PL → 凸体 BM → entropy BM) で L-BM1 を
> 閉じる。本 plan は **EPI route** (1-D EPI → n-dim EPI → CT 17.7.4 で BM へ
> 変換) で同じ L-BM1 を閉じる、**直交 ルート**である。closure plan が
> 「BM は Mathlib 壁不在 (Fubini 配線のみ)」を主張するのに対し、本 plan は
> 「1-D EPI Stam 解析の壁 (b) が **前提**」となるため stand-alone closure では
> ない: **EPI 1-D 全閉鎖を要する** vs **n-dim 拡張のみで足りる** の判断 (§撤退ライン)
> が本 plan の主な technical decision 点。実装する場合は closure plan と独立に
> publish するか、closure plan の体積版段階着地で済ませて本 plan を skip するか
> を Phase 0 で決める。

## 進捗

- [ ] Phase 0 — Mathlib + InformationTheory 既存 EPI / BM API 在庫 + CT 17.7.4 textbook flow 固定 📋 → [`brunn-minkowski-from-epi-mathlib-inventory.md`](brunn-minkowski-from-epi-mathlib-inventory.md) (未起草、Phase 0 で着手)
- [ ] Phase 1 — 1-D EPI 残仮定の整理 (Stam 解析の壁 (b) status 確定 + 本 plan が前提として受け取る形を honest predicate で固定) 📋
- [ ] Phase 2 — n-dim EPI 拡張 (coordinate-wise iteration、1-D EPI を `Fin n` で繰り返し適用) 📋
- [ ] Phase 3 — CT 17.7.4 bridge (n-dim EPI ↔ n-dim BM、entropy 形 ⇔ 体積 superlevel 形の同等性) 📋
- [ ] Phase 4 — L-BM1 discharge restate + 親 BM headline rewire (`brunn_minkowski_entropy_inequality` を本 plan の chain で `:= h_bm` を経由しない genuine 形に置換) 📋
- [ ] Phase V — verify + 親 plan 反映 + 判断ログ確定 📋

## ゴール / Approach

### Goal

`InformationTheory/Shannon/BrunnMinkowski.lean:188` の `brunn_minkowski_entropy_inequality`
(現在 `:= h_bm_entropy_assumed` で結論を仮説として受け取る pass-through) を、
**EPI 経由の chain** から genuine に導出する形に rewire する。chain の形:

```
[1-D EPI]                              ← InformationTheory 既存 (Gaussian case full、
   │                                     general case は Stam 解析の壁 (b) 残)
   │ coordinate-wise iteration on `Fin n`
   ▼
[n-dim EPI]                            ← Phase 2 で新規 publish
   │                                     `exp((2/n) h_n(X+Y)) ≥ exp((2/n) h_n(X))
   │                                       + exp((2/n) h_n(Y))` for `Fin n → ℝ`
   │ CT 17.7.4 / 17.9.2 同等性
   ▼
[n-dim Brunn-Minkowski (entropy form)] ← Phase 3 で n-dim EPI から導出
   │                                     これが現 `IsBrunnMinkowskiEntropyHypothesis`
   │                                     の結論
   │ restate
   ▼
`brunn_minkowski_entropy_inequality_from_epi` (Phase 4 新規 publish、
genuine 形、`:= h_bm` を経由しない)
```

完了時:

- `InformationTheory/Shannon/BrunnMinkowskiFromEPI.lean` (新規, 推定 ~400-700 行) に
  上記 chain を publish。
- 旧 `brunn_minkowski_entropy_inequality` (`BrunnMinkowski.lean:188`、L-BM1
  pass-through) は **deprecated として残す** (signature 互換、過去参照のため)。
- `InformationTheory.lean` に `import InformationTheory.Shannon.BrunnMinkowskiFromEPI` 1 行追加。

### Approach (overall strategy / shape of solution)

**全体の shape** — EPI route の 3 段 chain は **各段が独立な hypothesis pass-through
で組める** ことが鍵。closure plan の Fubini 帰納が「1D PL → n-dim PL の単一
contiguous induction」だったのに対し、本 plan は「1-D EPI → n-dim EPI (coord
iterate) → CT 17.7.4 (entropy ↔ 体積) → BM」の **3 別 file 直列接続** となる。

1. **1-D EPI を black-box 化** (Phase 1)。`InformationTheory/Shannon/EntropyPowerInequality.lean`
   の主定理 `entropy_power_inequality` (`:230`) は現在
   - `h_stam : IsStamInequalityResidual X Y P` (`:187`、Stam 解析の壁 (b)、
     intentional staged)
   - `h_bridge : IsStamToEPIBridge X Y P` (`:203`、Cover-Thomas Lemma 17.7.3
     coupling、これも staged)

   の 2 つ honest residual を受け取って `h_bridge h_stam` で着地する **non-circular
   形** (本体は `:= h` 循環ではない; `h_bridge` は function type で結論型と異なる)。
   本 plan は **この 2 residual を前提として受け継ぐ** か、それとも本 plan 内で
   さらに Phase を立てて discharge するかを Phase 1 で判断する。staged 前提を
   引き継ぐ場合、本 plan の n-dim BM 結論にも同 residual が `IsStamInequalityResidual`
   ベクトル形 (`Fin n` 個) として propagate する。

2. **n-dim EPI は coordinate-wise iteration で組む** (Phase 2)。Cover-Thomas
   Ch.17.7 の n-dim EPI 形は、各 coordinate `i : Fin n` 上で 1-D EPI を独立に
   適用 + sum across coordinates、というのが教科書の流儀。本 plan も同じ:
   `X, Y : Ω → (Fin n → ℝ)` の `i`-th projection `X i, Y i : Ω → ℝ` に対し
   1-D EPI を `i` 個 適用し、`Fin n` 上で sum or product。**鍵となる Mathlib-shape
   判断**: 結論を `exp((2/n)·h_n(X+Y))` 形 (`h_n` は n-dim differential entropy) に
   したいので、1-D EPI 結論 `exp(2·h_1(X_i + Y_i))` を `Fin n` で集約する際の係数
   `2 → 2/n` 変換を `Real.exp_sum` / `Finset.sum` / `n` 乗根経由で吸収する。

   ただし **n-dim differential entropy** (`differentialEntropy_nDim` または
   `jointDifferentialEntropyPi`) と 1-D entropy `h_1` の **積分分解** (independent
   coordinate なら `h_n(X) = Σ h_1(X_i)`, dependent なら subadditivity のみ)
   が必要。InformationTheory 既存:
   - `MultivariateDiffEntropy.jointDifferentialEntropyPi` (`:58`, genuine 構造)
   - `MultivariateDiffEntropy.jointDifferentialEntropyPi_le_sum` (`:272`,
     subadditivity)

   が使える。**等式 (independent coordinate)** が必要なら追加 lemma が要る (Phase
   0 inventory で確認)。

3. **CT 17.7.4 bridge は entropy ↔ 体積形の同等性** (Phase 3)。Cover-Thomas
   Ch.17.7 Theorem 17.7.4 は「n-dim EPI ⇔ n-dim BM」の同等性を述べる定理で、
   片方向 (EPI → BM) は **典型集合 (typicality) の体積 BM 不等式** を経由する
   流儀。本 plan は片方向 EPI → BM のみ必要なので、textbook flow:
   - n-dim EPI: `exp((2/n) h_n(X+Y)) ≥ exp((2/n) h_n(X)) + exp((2/n) h_n(Y))`
   - 両辺を uniform on 典型集合 / convex body の entropy = `log vol` (max-entropy
     principle, Phase 3 で Jensen で示すか hypothesis 化) で `vol^{1/n}` 形に
     特化
   - 結論: `vol(supp(X+Y))^{1/n} ≥ vol(supp X)^{1/n} + vol(supp Y)^{1/n}`
     = 凸体 BM (CT 17.9.3 / Minkowski)

   さらに entropy 形 BM そのもの (CT 17.9.2,
   `IsBrunnMinkowskiEntropyHypothesis` の結論) は **n-dim EPI と defeq**: 両者
   とも `exp((2/n) h(X+Y)) ≥ exp((2/n) h(X)) + exp((2/n) h(Y))` の形をしており、
   n-dim EPI のスコープが `entropyPower_nDim` を使うなら **そのまま BM 結論**。
   この場合 Phase 3 は「signature 整合性」のみ (型変換 / `entropyPower_nDim`
   定義との一致確認) で済む。Phase 0 で **CT 17.9.2 と 17.7.4 のどちらが本 plan
   の参照経路か**を確定する (現状 BrunnMinkowski.lean docstring は 17.7.4 と
   17.9.2 を交互に挙げている; 教科書定義上、17.9.2 = entropy 形 BM が直接の
   結論で、17.7.4 は EPI と BM の "equivalent form" 同等性メタ定理)。

4. **Mathlib-shape-driven 設計判断** (CLAUDE.md):
   - **n-dim entropy** は `jointDifferentialEntropyPi` (`MultivariateDiffEntropy.lean:58`)
     を採用 (closure plan と同じ選択)。これにより closure plan で着地予定の
     `brunn_minkowski_entropy_jointPi` (closure Phase 3) と本 plan の最終
     headline は **同じ signature** に揃う (重複 publish 回避の合流点を Phase 4
     で判断ログに記録)。
   - **n-dim EPI 結論形** は `entropyPower_nDim n h_n (P.map (X+Y))
     ≥ entropyPower_nDim n h_n (P.map X) + entropyPower_nDim n h_n (P.map Y)`
     で固定 (現 BM 結論と signature 一致、Phase 3 の bridge が型変換不要に
     なる)。
   - **coordinate iteration** は `Finset.induction_on (Finset.univ : Finset (Fin n))`
     ではなく **`Fin n` の `Nat.rec` 帰納** で組む (`Fin.snoc` で 1 次元ずつ
     拡張、独立性は `IndepFun_pi` / `iIndepFun` で運ぶ)。1-D EPI を base case
     で適用、step case で帰納仮定 (n-dim EPI) + 1-D EPI + 残り 1 coord 独立性。
   - **撤退時の honest hypothesis**: 1-D EPI 全閉鎖が要らない (n-dim 拡張のみで
     足りる) 場合は `IsStamInequalityResidual` を **既存 staged predicate のまま
     上に積む**。1-D EPI 全閉鎖が必要な場合 (例: CT 17.7.4 が 1-D 等号 case を
     使う) は本 plan は EPI Stam 残タスクに **transitively block** され、本 plan
     を **撤退** して closure plan (Fubini 直接路) に流す判断を §撤退ライン に
     記述。

### Approach 図

```
[Phase 0] inventory                                   ← 在庫 + textbook flow 確定
          ──────────────────────────────────────────
[Phase 1] 1-D EPI 残仮定の整理                          ← Stam 解析の壁 (b) status
          IsStamInequalityResidual (既存 :187)        ← 前提として propagate
          IsStamToEPIBridge        (既存 :203)         ← 前提として propagate
          ──────────────────────────────────────────
[Phase 2] n-dim EPI (coordinate iterate)               ← `Fin n` rec、新規 file
          entropy_power_inequality_nDim                   `BrunnMinkowskiFromEPI.lean`
          (independent coordinate 形)
          ──────────────────────────────────────────
[Phase 3] CT 17.7.4 bridge (entropy ↔ BM)              ← signature 整合 + 凸体
          brunn_minkowski_from_nDim_epi                  特化 (max-entropy)
          ──────────────────────────────────────────
[Phase 4] L-BM1 discharge restate                      ← `:= h_bm` を経由しない
          brunn_minkowski_entropy_inequality_from_epi    genuine chain で publish
          ──────────────────────────────────────────
[Phase V] verify + 反映                                 ← `lake env lean` silent
```

## 新規 file

- `InformationTheory/Shannon/BrunnMinkowskiFromEPI.lean` (新規, 推定 **~400-700 行**)
  - imports (pinpoint, `import Mathlib` 禁止):
    ```
    import InformationTheory.Shannon.BrunnMinkowski
    import InformationTheory.Shannon.EntropyPowerInequality
    import InformationTheory.Shannon.MultivariateDiffEntropy
    import InformationTheory.Shannon.DifferentialEntropy
    import Mathlib.Probability.Independence.Basic
    import Mathlib.MeasureTheory.Constructions.Pi
    import Mathlib.Analysis.SpecialFunctions.Exp
    ```
  - namespace: `InformationTheory.Shannon.BrunnMinkowskiFromEPI`
- `docs/shannon/brunn-minkowski-from-epi-mathlib-inventory.md` (新規, Phase 0
  成果物、mathlib-inventory subagent に委譲)
- 既存 file 編集なし (Phase 4 の restate は新 file に publish、旧 headline は
  signature 互換のため変更しない)

## Phase 詳細

---

### Phase 0 — Mathlib + InformationTheory 既存 EPI / BM API 在庫 + CT 17.7.4 textbook flow 固定 📋

`proof-log: no` (在庫確認のみ)。

**ゴール**: Phase 1-4 で消費する既存 genuine 補題の **正確な signature** を確定し、
CT 17.7.4 textbook flow (n-dim EPI ⇔ n-dim BM の同等性) のどちら方向を使うかを
固定する。**mathlib-inventory subagent** に委譲し、結構を
`docs/shannon/brunn-minkowski-from-epi-mathlib-inventory.md` に出力。
CLAUDE.md「Subagent Inventory of Mathlib Lemmas」要件 (file:line + 全 signature +
type-class verbatim + conclusion form 完コピ) 厳守。

#### 在庫対象 (subagent prompt から省略しない)

##### InformationTheory 既存 EPI 群 (再利用)

- [ ] **1-D EPI 主定理**: `InformationTheory.Shannon.EntropyPowerInequality.entropy_power_inequality`
  (`EntropyPowerInequality.lean:230`). 入力: `P : Measure Ω`, `X Y : Ω → ℝ`,
  `Measurable`, `IndepFun`, `IsStamInequalityResidual X Y P`,
  `IsStamToEPIBridge X Y P`. 出力: `entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)`.
- [ ] **1-D `entropyPower` 定義**: `EntropyPowerInequality.entropyPower`
  (`:?`). 形: `Real.exp (2 * differentialEntropy μ)`.
- [ ] **Gaussian saturation**: `EntropyPowerInequality.entropy_power_inequality_gaussian_saturation`
  (`:266`). 等号、full discharge。本 plan は **n-dim Gaussian case** で同じ
  full discharge を狙う (撤退時の段階着地点)。
- [ ] **Stam residual / bridge predicates** (継承元):
  `IsStamInequalityResidual` (`:187`、Fisher 値表 keyed),
  `IsStamToEPIBridge` (`:203`、function type, 結論 ≠ 仮説 ⇒ honest)。

##### InformationTheory 既存 BM 群 (signature 整合先)

- [ ] **n-dim entropy power**: `BrunnMinkowski.entropyPower_nDim`
  (`BrunnMinkowski.lean:98`). 形: `Real.exp ((2/n) * h μ)`, `h : Measure (Fin n → ℝ) → ℝ`.
- [ ] **n-dim BM 結論 predicate**: `BrunnMinkowski.IsBrunnMinkowskiEntropyHypothesis`
  (`:132`). 形: `entropyPower_nDim n h (P.map (X+Y)) ≥ entropyPower_nDim n h (P.map X) + entropyPower_nDim n h (P.map Y)`.
  **本 plan の最終 headline はこれと同 signature を提供** (genuine chain で)。
- [ ] **n-dim BM 主定理 (pass-through)**: `BrunnMinkowski.brunn_minkowski_entropy_inequality`
  (`:188`). 本体 `:= h_bm_entropy_assumed` (`:197`). **本 plan で genuine 形に
  rewire 対象**。

##### InformationTheory 既存 multivariate entropy

- [ ] **jointDifferentialEntropyPi**: `MultivariateDiffEntropy.jointDifferentialEntropyPi`
  (`:58`). 形: `∫ z, negMulLog ((μ.rnDeriv volume z).toReal) ∂volume`. 型クラス前提
  verbatim 確認 (`[IsProbabilityMeasure μ]`, `[∀ i, IsProbabilityMeasure (μ.map (· i))]`,
  + honest hyp `h_marg_ac`, `hμ_ac`, `h_joint_ac`, `h_llr_split`, `h_int_marg`,
  `h_int_joint`, `h_marg_id`)。
- [ ] **jointPi subadditivity**: `MultivariateDiffEntropy.jointDifferentialEntropyPi_le_sum`
  (`:272`). 形: `jointDifferentialEntropyPi μ ≤ Σ_i h_1 (μ.map (· i))`. **本 plan
  の Phase 2 coord iteration の方向 (`≤`)** と整合 — 但し EPI は `≥` なので
  方向逆転に注意 (entropy power の `exp` で `Σ h_i` ↔ `Π exp(h_i)` 変換 + n-dim
  EPI が下から押さえる形に綴じる)。
- [ ] **independent case 等式**: independent coordinate での `h_n = Σ h_1` 等式
  (subadditivity の等号成立条件)。InformationTheory に既存か Mathlib に既存か Phase 0
  で loogle 確認 (`MultivariateDiffEntropy.jointDifferentialEntropyPi_eq_sum_of_indep`
  のような名前で探す)。

##### Mathlib 在庫 (要 loogle)

- [ ] **`Fin n` 上の iteration / `Fin.snoc`**: `Fin.cases`, `Fin.snoc`, `Fin.consInduction`
  の signature verbatim。Phase 2 coord rec の base/step を決める。
- [ ] **`iIndepFun` / `IndepFun_pi`**: 独立性を `Fin n` で扱う API。
  `ProbabilityTheory.iIndepFun`, `iIndepFun.indepFun` で 1-D pair 取り出しが
  できるか。
- [ ] **`Measure.pi_map_*`**: product 測度と push-forward の整合。`Measure.pi`
  vs `Measure.map (fun ω i => X i ω) P` 等。
- [ ] **`Real.exp_sum` / `Finset.sum_exp`**: `exp(Σ a_i) = Π exp(a_i)` の方向
  (本 plan は `Π exp(2 h_1)` を集約して `exp((2/n) Σ h_1)` に変換、もしくは
  逆方向)。`Finset.prod_exp` / `Real.exp_sum` 確認。

#### CT 17.7.4 textbook flow の固定

- [ ] **CT 17.7.4 がカバーする方向**: 教科書 Theorem 17.7.4 は EPI ⇔ BM の
  同等性 (双方向)。本 plan は **EPI → BM** のみ必要。textbook の証明流儀:
  - **EPI → BM**: uniform on convex body の entropy = `log vol` を使い、entropy
    形 EPI の両辺を `exp` で持ち上げ、`vol^{1/n}` 形に置換。
  - **BM → EPI**: 典型集合 (typicality) の体積を BM で評価し、AEP 経由で
    `e^{nh}` ≈ typical set 体積。これは本 plan 不要。
- [ ] **CT 17.9.2 (entropy 形 BM) と CT 17.7.4 の関係**: 17.9.2 は **n-dim BM
  そのもの**を述べる。17.7.4 は 17.9.2 ⇔ n-dim EPI を述べる metalemma。
  **本 plan の最終 headline 17.9.2 結論は n-dim EPI と defeq (Cover-Thomas
  Ch.17.9 が示す)** — この場合 Phase 3 の bridge は型変換のみ。Phase 0 で
  textbook を再確認し判断ログに記録。

#### Done 条件

- 上記 inventory が `docs/shannon/brunn-minkowski-from-epi-mathlib-inventory.md`
  に subagent 出力で揃う (file:line + verbatim signature)。
- **CT 17.7.4 vs 17.9.2 のどちらが本 plan の参照経路か**確定 (Phase 3 の
  signature 設計に直結)。
- 1-D EPI 全閉鎖が要るかどうか (Stam 解析の壁 (b) を本 plan が transitively
  block されるか) の判断材料が揃う。

---

### Phase 1 — 1-D EPI 残仮定の整理 📋

`proof-log: yes` (撤退判断ログ必須)。**推定 ~50-100 行** (predicate 整理のみ、
本体は `BrunnMinkowskiFromEPI.lean` の前段)。

**ゴール**: 1-D EPI の honest residual (`IsStamInequalityResidual`,
`IsStamToEPIBridge`) を本 plan の n-dim chain に propagate する形を確定する。

#### step

- [ ] **本 plan が前提として受け取る形を honest predicate で固定**:
  ```lean
  /-- n-dim EPI が前提とする 1-D EPI residual の `Fin n` 個 vectorisation。
  各 coordinate `i : Fin n` について Stam residual + bridge を要求する。 -/
  def IsStamInequalityResidual_nDim {Ω : Type*} [MeasurableSpace Ω]
      (n : ℕ) (X Y : Ω → (Fin n → ℝ)) (P : Measure Ω) : Prop :=
    ∀ i : Fin n, IsStamInequalityResidual (fun ω => X ω i) (fun ω => Y ω i) P

  def IsStamToEPIBridge_nDim {Ω : Type*} [MeasurableSpace Ω]
      (n : ℕ) (X Y : Ω → (Fin n → ℝ)) (P : Measure Ω) : Prop :=
    ∀ i : Fin n, IsStamToEPIBridge (fun ω => X ω i) (fun ω => Y ω i) P
  ```
  入力型: `Ω, X, Y, P, n`. 出力型: `Prop` (`Fin n` 上の universal quantification).
  **honest**: 結論 (n-dim BM) と defeq でない、各 coord での Stam inverse
  triangle (`1/J(X_i+Y_i) ≥ 1/J(X_i) + 1/J(Y_i)`) で n-dim BM の値表とは
  完全に異なる構造。`docstring` で「NOT a discharge、1-D EPI Stam 解析の壁
  (b) の n-dim propagation」と明示。

- [ ] **判断**: 本 plan は **1-D EPI 全閉鎖を要求しない**選択を採用 (entropy
  Stam の解析の壁 (b) は intentional staged のまま、その上に n-dim 拡張のみ
  積み上げる)。**理由**: closure plan が「BM は Mathlib 壁不在」と主張する以上、
  EPI route は **Stam の壁 (b) で transitively block** される時点で closure plan
  に対して劣位。本 plan を maintain する価値は: (i) CT 教科書順の literature 整合、
  (ii) Gaussian case で n-dim EPI が full discharge できる可能性 (Phase 2 段階
  着地)、(iii) closure plan の Fubini が詰まった場合の fallback。

- [ ] **撤退時 (1-D EPI 全閉鎖が要ると判明した場合)**: 本 plan を撤退、closure
  plan 一本に統合する判断ログを残す。判断は Phase 0 inventory 結果次第。

#### Done 条件

- `IsStamInequalityResidual_nDim` / `IsStamToEPIBridge_nDim` が
  `BrunnMinkowskiFromEPI.lean` に 0 sorry で定義済 (Prop 定義のみ、proof body
  なし)。
- 判断ログに「1-D EPI 全閉鎖を本 plan は要求しない、Stam 解析の壁 (b) は
  propagate する」が記録済。

---

### Phase 2 — n-dim EPI (coordinate iterate) 📋

`proof-log: yes`。**推定 ~150-300 行** (本 plan の最大ブロック)。

**ゴール**: 1-D EPI を `Fin n` 上で iterate し、n-dim EPI を publish。

#### step

- [ ] **base case (n = 1)**: `Fin 1 → ℝ ≃ ℝ` 経由で 1-D EPI を直接適用。
  入力型: 1-D EPI residual + bridge (`Fin 1` 上の `IsStamInequalityResidual_nDim`).
  出力型: `entropyPower_nDim 1 h_1 (P.map (X+Y)) ≥ ...`. Phase A の `entropyPower_nDim_one`
  (`BrunnMinkowski.lean:269`、`entropyPower_nDim 1 h μ = Real.exp (2 * h μ)`) を
  使い、1-D `entropyPower` と係数 2 で defeq。

- [ ] **step case (n → n+1)**: `Fin.snoc` で 1 coordinate 拡張。帰納仮定 + 残り
  1 coord 上の 1-D EPI + 独立性を使う。**鍵となる shape**: n-dim entropy が
  independent coordinate で `h_{n+1} = h_n + h_1` に分解できるかが判定点。
  - **independent coordinate 等式が Mathlib/InformationTheory にあれば**: それを使い、
    `exp((2/(n+1)) h_{n+1})` を `exp((2/(n+1)) h_n + (2/(n+1)) h_1)` に分解、
    `exp_add` で `exp((2/(n+1)) h_n) * exp((2/(n+1)) h_1)` 形に。あとは
    係数 `2/(n+1)` の `n/(n+1) + 1/(n+1)` 分解 + AM-GM/Hölder で帰納仮定 +
    1-D EPI を合成。
  - **等式がない場合 (subadditivity のみ)**: 帰納が片方向不等式で walks (EPI は
    `≥` だが subadditivity は `≤` で方向逆)、**Phase 2 撤退** → Phase 2 を
    honest hypothesis `IsEntropyAdditivityHyp_indep` (実際 `=` 命題、`:= True`
    禁止) に外出しして抜く。

- [ ] **n-dim EPI 主定理 publish**:
  ```lean
  theorem entropy_power_inequality_nDim {Ω : Type*} {mΩ : MeasurableSpace Ω}
      (P : Measure Ω) [IsProbabilityMeasure P]
      (n : ℕ) (h_n : Measure (Fin n → ℝ) → ℝ)
      (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
      (hXY : IndepFun X Y P)
      (h_stam_n : IsStamInequalityResidual_nDim n X Y P)
      (h_bridge_n : IsStamToEPIBridge_nDim n X Y P)
      (_h_entropy_decomp : ...) -- coordinate 分解の何らか hypothesis (honest)
      :
      entropyPower_nDim n h_n (P.map (fun ω => X ω + Y ω))
        ≥ entropyPower_nDim n h_n (P.map X) + entropyPower_nDim n h_n (P.map Y)
  ```
  これが本 plan の中核成果物 (n-dim EPI の publish 自体に独立価値)。

- [ ] **Gaussian saturation case (full discharge 候補)**: n-dim Gaussian
  (各 coord 独立 1-D Gaussian) に対し n-dim EPI は等号成立。1-D 等号
  (`entropy_power_inequality_gaussian_saturation`) を `Fin n` で iterate し、
  `gaussianReal_pi` 型の n-dim Gaussian product 構造で集約。**段階着地点 1**:
  Phase 2 Gaussian case だけでも本 plan に独立価値がある。

#### 撤退ライン (Phase 内)

- **>300 行で Fin n rec が詰まる**: `Fin n` rec を諦め、coordinate decoupling
  を honest hypothesis (`IsEPICoordDecouplingHyp`, 実 `≥` 命題) に外出しして
  Phase 2 を閉じる。**critical**: ここで `:= True` placeholder にしない
  (CLAUDE.md「検証の誠実性」)、必ず実 `Prop` 命題で残す。
- **independent coordinate 等式が Mathlib/InformationTheory 双方に不在**: max-entropy
  (Jensen 凹性) で `≤` 方向のみ取り、EPI の `≥` 方向は別 lemma に分離。

#### Done 条件

- `entropy_power_inequality_nDim` が 0 sorry (撤退時は honest hypothesis 1-2 本
  追加で着地)。
- Gaussian n-dim saturation が full discharge (段階着地点 1 達成、Phase 3-4 が
  詰まっても n-dim EPI の Gaussian case は genuine に立つ)。

---

### Phase 3 — CT 17.7.4 bridge (entropy ↔ BM) 📋

`proof-log: yes`。**推定 ~50-150 行** (Phase 0 で 17.9.2 vs 17.7.4 の判断次第)。

**ゴール**: n-dim EPI (Phase 2) と n-dim BM (現 `IsBrunnMinkowskiEntropyHypothesis`
の結論) の同等性 bridge を publish。

#### step

##### Case A: 17.9.2 が n-dim EPI と defeq (Phase 0 で確定する想定)

- [ ] **signature 整合性 lemma**: `entropy_power_inequality_nDim` の結論と
  `IsBrunnMinkowskiEntropyHypothesis n h X Y P` の unfold 形 (= 結論そのもの)
  が defeq であることを確認する 1 行 lemma:
  ```lean
  theorem brunn_minkowski_entropy_hypothesis_of_epi_nDim
      ... (h_epi_n : entropyPower_nDim n h_n ... ≥ ...) :
      IsBrunnMinkowskiEntropyHypothesis n h_n X Y P :=
    h_epi_n
  ```
  入力型: n-dim EPI 結論. 出力型: `IsBrunnMinkowskiEntropyHypothesis ...`.
  **defeq なので本体は `h_epi_n`** (これは循環ではない:
  `IsBrunnMinkowskiEntropyHypothesis` は parametric 定義で、ここでは n-dim EPI
  から **genuine に得た** 不等式 `h_epi_n` を hypothesis predicate に持ち上げて
  いる)。

##### Case B: 17.7.4 が必要 (17.9.2 と n-dim EPI が異なる shape)

- [ ] **entropy 形 → 体積形 bridge**: uniform on convex body の max-entropy
  (`h(uniform) = log vol`) を経由して `vol^{1/n}` 形 BM を導出。closure plan
  Phase 3 と同じ max-entropy step を再利用。
- [ ] **本 plan は entropy 形 BM (17.9.2) で着地**するため、Case B は **deferred**
  (体積形 BM は closure plan に任せる)。

#### Done 条件

- Case A 採用なら 1-2 lemma で完了 (~30 行)。Case B 採用なら closure plan と
  flag duplication なきよう判断ログに合流点記録。
- `IsBrunnMinkowskiEntropyHypothesis n h X Y P` を n-dim EPI chain から
  genuine に produce する lemma が publish 済。

---

### Phase 4 — L-BM1 discharge restate + 親 BM headline rewire 📋

`proof-log: yes`。**推定 ~50-100 行**。

**ゴール**: 親 BM `brunn_minkowski_entropy_inequality` の `:= h_bm` pass-through
を、本 plan の chain で genuine 形に restate して publish。

#### step

- [ ] **restate 主定理**:
  ```lean
  /-- **Brunn-Minkowski inequality (entropy form) from EPI route**
  (Cover-Thomas Theorem 17.9.2、EPI 経由 genuine 形).

  親 `BrunnMinkowski.brunn_minkowski_entropy_inequality` は L-BM1
  pass-through (`:= h_bm`) で結論を仮説として受け取るが、本 restate は
  n-dim EPI chain (Phase 2-3) から genuine に導出する。

  staged: Stam 解析の壁 (b) は本 plan が前提として propagate する
  (`IsStamInequalityResidual_nDim` / `IsStamToEPIBridge_nDim`)。これらが
  discharge されない限り本 chain も transitively staged だが、`:= h_bm`
  循環ではない (residual の型は n-dim EPI conclusion と異なる)。 -/
  theorem brunn_minkowski_entropy_inequality_from_epi
      {Ω : Type*} {mΩ : MeasurableSpace Ω}
      (P : Measure Ω) [IsProbabilityMeasure P]
      (n : ℕ) (h_n : Measure (Fin n → ℝ) → ℝ)
      (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
      (hXY : IndepFun X Y P)
      (h_stam_n : IsStamInequalityResidual_nDim n X Y P)
      (h_bridge_n : IsStamToEPIBridge_nDim n X Y P)
      (h_entropy_decomp : ...) :  -- Phase 2 で確定する honest hyp
      entropyPower_nDim n h_n (P.map (fun ω => X ω + Y ω))
        ≥ entropyPower_nDim n h_n (P.map X) + entropyPower_nDim n h_n (P.map Y)
  ```
  本体: Phase 2 `entropy_power_inequality_nDim` + Phase 3 bridge の合成
  (Case A なら 1 行)。

- [ ] **n-dim Gaussian saturation (full discharge corollary)**:
  ```lean
  theorem brunn_minkowski_entropy_inequality_from_epi_gaussian_saturation
      ... (X, Y が各 coord 独立 Gaussian, variance 非零) ... :
      entropyPower_nDim n h_n (P.map (X+Y))
        = entropyPower_nDim n h_n (P.map X) + entropyPower_nDim n h_n (P.map Y)
  ```
  Phase 2 の Gaussian saturation を持ち上げ、n-dim Gaussian case で full
  discharge (撤退ラインなし)。**段階着地点 2**: BM の Gaussian case が genuine
  に閉じる (n-dim entropy 等号、Stam staged 不要)。

- [ ] **旧 headline の処理**: 旧 `BrunnMinkowski.brunn_minkowski_entropy_inequality`
  (`:188`) は signature 互換のまま維持 (`@[deprecated]` attribute 検討可、
  closure plan Phase 4 と同じ運用)。**取り消し線にしない** (過去参照のため)。

#### Done 条件

- `brunn_minkowski_entropy_inequality_from_epi` が 0 sorry (Phase 1-3 chain で
  着地)。
- n-dim Gaussian saturation case が full discharge (段階着地点 2)。

---

### Phase V — verify + 親 plan 反映 + 判断ログ確定 📋

`proof-log: no`。

- [ ] `lake env lean InformationTheory/Shannon/BrunnMinkowskiFromEPI.lean` silent (0
  error / 0 sorry / 最小 warning)。
- [ ] `InformationTheory.lean` に `import InformationTheory.Shannon.BrunnMinkowskiFromEPI`
  1 行追加。
- [ ] 親 `brunn-minkowski-moonshot-plan.md` 末尾「Full genuine closure (後続 plan)」
  節に本 plan へのポインタ追記 (closure plan のポインタは既存、本 plan を 2 本目
  として並列に並べる)。
- [ ] 残存 honest hypothesis (`IsStamInequalityResidual_nDim`,
  `IsStamToEPIBridge_nDim`, Phase 2 の entropy decomp hyp) を棚卸しし、各々が
  `:= True` ではなく実内容を持つこと + 結論と型が異なることを確認、proof-log
  に列挙。
- [ ] sibling `brunn-minkowski-closure-plan.md` の判断ログに本 plan との関係
  (両 plan 並列、段階着地点共有) を append。

---

## 撤退ライン (plan 全体)

### 段階着地点

- **段階着地点 1 (Phase 2 Gaussian only)**: n-dim Gaussian case のみ full
  discharge。Phase 3-4 が詰まっても、n-dim EPI Gaussian case publish は本 plan
  独立の成果。
- **段階着地点 2 (Phase 4 Gaussian only)**: BM 形に restate した n-dim Gaussian
  case が full discharge。`brunn_minkowski_entropy_inequality_from_epi_gaussian_saturation`
  publish。
- **段階着地点 3 (Phase 4 general)**: 一般 RV BM が genuine chain で立つ (Stam
  staged propagate 含む)。**本 plan の主目標**。

### 撤退判断

- **1-D EPI 全閉鎖が必要と判明 (Phase 0)**: 本 plan を撤退。closure plan
  (Fubini 直接路) 一本に統合。本 plan は判断ログのみ残す。
- **Phase 2 Fin n rec が詰まる**: honest hypothesis (`IsEPICoordDecouplingHyp`)
  に外出し、Phase 2 を段階着地点 1 で閉じる。Phase 3-4 は scope 縮小。
- **Phase 3 で 17.7.4 path が要る (Case B)**: max-entropy step を closure plan
  Phase 3 と統合。本 plan は entropy 形のみで着地、体積形は closure に任せる。
- **Phase 4 で旧 headline rewire が破壊的になる**: 旧 `brunn_minkowski_entropy_inequality`
  はそのまま残し、新 file `brunn_minkowski_entropy_inequality_from_epi` で
  parallel publish (deprecation は別 PR)。

### `:= True` 禁止確認

本 plan の honest predicate 群はすべて **実内容を持つ `Prop`** (結論と型が異なる):

- `IsStamInequalityResidual_nDim`: `Fin n` 上の Stam inverse triangle (`1/J ≥ 1/J + 1/J`),
  BM 結論 (`exp((2/n)h) ≥ ...`) と完全に別構造。
- `IsStamToEPIBridge_nDim`: 関数型 `IsStamRes → IsEPI` (`Fin n` 個 collection)、
  結論と defeq 不可能。
- Phase 2 の `_h_entropy_decomp` (採用する場合): 等式 (`h_{n+1} = h_n + h_1`) で
  BM 不等式とは別の型。

CLAUDE.md「検証の誠実性」遵守。

---

## 既存 plan との scope 区別 (重要)

| plan | route | 主結論 | 1-D EPI 依存 | 残 staged |
|---|---|---|---|---|
| `brunn-minkowski-moonshot-plan.md` (publish 済) | hypothesis pass-through | `:= h_bm` で結論を仮説化 | なし (仮説で吸収) | L-BM1 (defect, 本 plan の対象) |
| `brunn-minkowski-closure-plan.md` (起草済) | **Fubini 直接路** (1D PL → n-dim PL → 凸体 BM → entropy BM) | n-dim PL Fubini で genuine | **不要** (BM は EPI 経由しない) | Fubini 配線 ~400-600 行 |
| `brunn-minkowski-from-epi-discharge-plan.md` (本 plan) | **EPI route** (1-D EPI → n-dim EPI → CT 17.7.4) | n-dim EPI から CT 同等性で genuine | **要** (Stam 解析の壁 (b) を propagate) | Stam 残 + n-dim 拡張 ~400-700 行 |

**両 closure route の並列価値**:

- closure plan は **Mathlib 壁不在**を主張 (Fubini 配線のみ) — 完了可能性最も高い。
- 本 plan は **CT 教科書順整合** (Cover-Thomas Ch.17.7.4 が EPI ⇔ BM を述べる
  ので、両方を持つことで textbook coverage を完成)。
- 一方を撤退して他方を採用、または両方を並列 publish (異なる headline 名で
  共存) は Phase 4 で判断。

**重複回避**: max-entropy step (uniform = log vol、Jensen) は closure plan
Phase 3 と本 plan Phase 3 Case B が両方使う可能性あり。共通 lemma 化を Phase 4
判断ログで記録。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-24 起草

- **本 plan の前提診断**: 親 BM moonshot は L-BM1 pass-through (`BrunnMinkowski.lean:132`
  の `IsBrunnMinkowskiEntropyHypothesis` が結論そのもの、honesty audit defect
  type ≡ conclusion)。本 plan は **EPI route での L-BM1 discharge** を目的とする
  別 plan として起草。closure plan (Fubini 直接路) と **直交**。
- **EPI route の前提**: 1-D EPI (`entropy_power_inequality`, `EntropyPowerInequality.lean:230`)
  は Stam 解析の壁 (b) を `IsStamInequalityResidual` + `IsStamToEPIBridge` で
  staged。本 plan は **これらを n-dim に propagate する** (`IsStamInequalityResidual_nDim`)
  形で、Stam 全閉鎖を要求しない選択を採用。
- **CT 17.7.4 vs 17.9.2 の判断は Phase 0 で確定**: textbook 17.9.2 が entropy
  形 BM の主定理、17.7.4 が EPI ⇔ BM の equivalent form metalemma。本 plan の
  最終 headline (entropy 形 BM) は 17.9.2 と直接対応、n-dim EPI と defeq の
  可能性が高い (Case A、Phase 3 が型変換 1 行で済む)。
- **closure plan との scope 区別**: closure plan が Fubini 直接路で「BM は
  Mathlib 壁不在」を主張する以上、本 plan の優位性は (i) CT 教科書順整合,
  (ii) Gaussian case n-dim full discharge, (iii) closure plan fallback の 3 点。
  **closure plan が成功するなら本 plan は撤退候補** だが、Stam 解析の壁 (b) の
  intentional staged 維持と整合する EPI route も separate に publish 価値あり
  (judgement: 両方並列 publish、headline は別名で共存)。

<!--
記録予定 (着手後):
- Phase 0 で CT 17.7.4 vs 17.9.2 の判断 (Case A / Case B 確定)。
- Phase 2 で `Fin n` rec が直接走るか、independent coordinate 等式 hypothesis に
  落とすか。
- Phase 4 で旧 `brunn_minkowski_entropy_inequality` を deprecate するか、両方
  並列 publish か。
- 1-D EPI Stam 解析の壁 (b) の closure status (本 plan の transitively staged
  の上限を決める外部依存)。
-->

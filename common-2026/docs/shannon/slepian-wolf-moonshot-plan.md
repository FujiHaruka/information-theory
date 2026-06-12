# Slepian–Wolf 単発 converse ムーンショット計画 🌙

**Status**: CLOSED ✅ — done (Ch.15 Slepian-Wolf; 3-bound single-shot converse `slepian_wolf_converse_single_shot` implemented, 0 sorry, honest i.i.d. hypotheses only).

> **Seed**: [`docs/moonshot-seeds.md`](../moonshot-seeds.md) Seed 3
>
> **Status (2026-05-10):** 起草。`InformationTheory/Shannon/{Converse, Bridge, Entropy, CondMutualInfo, DPI}.lean` + `InformationTheory/Fano/Measure.lean` 完成済を起点に、distributed source coding (Slepian–Wolf) の single-shot converse を分散版として組む。
>
> 実態整合 (2026-05-20): **DONE-HONEST-HYPS — Phase A-C 完了表記は CODE と一致 (実装済)**。`InformationTheory/Shannon/SlepianWolf.lean` (23831 B, 0 sorry) に 3-bound single-shot converse 実装済。`slepian_wolf_converse_single_shot` (SlepianWolf.lean:449) は `slepian_wolf_converse_X`/`_Y`/`_sum` (それぞれ実証明 — side-info Fano + entropy chain rule) を `⟨_, _, _⟩` で束ねた実 converse (X/Y/sum bound、honest hyp `2 ≤ Fintype.card`)。FLAW なし。

## 進捗

- [x] Phase 0 — Mathlib + 既存 InformationTheory API インベントリ ✅ → [slepian-wolf-mathlib-inventory.md](slepian-wolf-mathlib-inventory.md)
- [x] Phase A — side info 入り Fano wrapper + `entropy_le_log_card` ✅ (2026-05-10)
- [x] Phase B — 3 bound (X / Y / sum) の本体実装 ✅ (2026-05-10)
- [x] Phase C — 3 bound 統合 + publish 形整理 ✅ (2026-05-10)

## ゴール / Approach

**ゴール**: 2 ソース `(Xs, Ys) : Ω → α × β` を独立 encoder `eX, eY` で圧縮し joint decoder `dec` で復号するとき、誤り率 `Pe ≤ ε` から rate に下界 3 本 (`log Mx ≥ H(X|Y) - δ`、`log My ≥ H(Y|X) - δ`、`log Mx + log My ≥ H(X,Y) - δ`) が出ることを single-shot で形式化する (Cover–Thomas 15.4)。

**Approach**: 新規 plumbing を「**side info 入り Fano (= paired conditioner で既存 Fano を呼ぶ thin wrapper) + 任意 μ の `H(W) ≤ log |W|`**」の 2 本に局所化し、3 bound はそれぞれ entropy chain rule + side info Fano + conditioning monotonicity の 3 段組で導く。3 bound はまず別 theorem 3 本として実装し、Phase C で 1 statement (構造体 or `And`) に統合可否を判断する。

```
Phase 0 : Mathlib + 既存 InformationTheory API 在庫 (paired conditioner Fano が成立するか裏取り)
          ─────────────────────────────────────────────────────────
Phase A : side info Fano (wrapper) + entropy_le_log_card (新規 ~30〜50 行)
          ─────────────────────────────────────────────────────────
Phase B : 3 bound 本体 (X bound 写経 → Y bound 対称 → sum bound chain rule)
          ─────────────────────────────────────────────────────────
Phase C : 3 bound 統合 + 1 statement 化判断 + publish 形仕上げ 🌙
```

### Approach の根幹: 側 info Fano は新規 lemma を作らない

side info `S` 入り Fano (`condEntropy μ Xs (Yo, sideInfo) ≤ binEntropy(Pe) + Pe · log(|X| - 1)`) は、既存 `fano_inequality_measure_theoretic` の `Yo` 引数を `(Yo, sideInfo) : Ω → Y × S` で呼ぶだけで成立する (Phase 0 で確認済み: `Y` 型 class は「任意の `MeasurableSpace`」なので `Y × S` でも適用可)。Phase A wrapper は実質「signature を読みやすくする」だけの ~15 行 thin wrapper。

### Approach の根幹: 3 bound 共通の Cover–Thomas 派生 chain

X bound (`log Mx ≥ H(X|Y) - δ`) の派生は以下の 5 段:

```
log Mx ≥ entropy μ (eX ∘ Xs)                          -- entropy_le_log_card (Phase A 新規)
       ≥ condEntropy μ (eX ∘ Xs) Ys                   -- conditioning monotonicity (既存)
       = entropy μ (eX∘Xs, Xs | Ys) - condEntropy μ Xs (eX∘Xs, Ys)
                                                       -- chain rule for cond entropy (既存 + 1 段 reshape)
       ≥ condEntropy μ Xs Ys - condEntropy μ Xs (eY∘Ys, eX∘Xs, Ys)
                                                       -- (Xs, eX∘Xs) は (Xs, eX∘Xs) の射影なので H(eX∘Xs, Xs|Ys) ≥ H(Xs|Ys)
                                                       -- conditioner を増やすと右辺は減らず (条件付け弱い側を取る)
       ≥ condEntropy μ Xs Ys - δ(Pe)                   -- side info Fano (Phase A wrapper)
```

Y bound は X / Y を入れ替えた対称形。sum bound は chain rule `H(X,Y) = H(X) + H(Y|X)` を使い、上記の 2 派生の合計から導く。

### ファイル構成 (Phase C 終了時)

```
InformationTheory/
  Shannon/
    SlepianWolf.lean          ← 新規。本 plan の主成果
                                ・fano_inequality_with_side_info (Phase A wrapper)
                                ・entropy_le_log_card (Phase A 新規)
                                ・slepian_wolf_converse_X (Phase B)
                                ・slepian_wolf_converse_Y (Phase B、対称)
                                ・slepian_wolf_converse_sum (Phase B)
                                ・slepian_wolf_converse_single_shot (Phase C 統合形)
```

`InformationTheory.lean` に `import InformationTheory.Shannon.SlepianWolf` を追記 (Converse の後)。

### 非ゴール

- **`n → ∞` 漸近 (asymptotic Slepian–Wolf)**: i.i.d. + AEP は別 seed (Seed 4) で扱う。本 plan は single-shot で閉じる
- **Random binning achievability**: converse の反対側 (rate region 内なら error → 0) は別ムーンショット
- **Side information at decoder のみの設定 (Wyner–Ziv)**: lossy 系の関連テーマ。本 plan の対象外
- **Mathlib upstream PR**: 副産物としては歓迎、能動的には追わない

---

## Phase 0 - Mathlib + 既存 InformationTheory API インベントリ ✅

### スコープ

- 軸 1: `shannon_converse_single_shot` 既存形と「Slepian–Wolf へ直接転用できるか」の判定
- 軸 2: side info 入り Fano が paired conditioner で出せるか (= 既存 `fano_inequality_measure_theoretic` の `Yo` 型が「任意の `MeasurableSpace`」になっているか)
- 軸 3: chain rule + conditioning monotonicity 既存補題位置 (`InformationTheory/Shannon/Entropy.lean`)
- 軸 4: encoder + 任意 μ の `H(W) ≤ log Fintype.card` の有無 (Loomis–Whitney の uniform 形式が代用可能か)
- 軸 5: 二者ペア確率変数の plumbing (`Measurable.prodMk` / `Measure.map_prod_map` / `Fintype.card_prod`)

### Steps

- [x] 軸 1〜5 を `slepian-wolf-mathlib-inventory.md` に CLAUDE.md「Subagent Inventory of Mathlib Lemmas」規約で記録
- [x] Mathlib に Slepian–Wolf 自体が無いことを `loogle` `"slepian"` / `"distributedSource"` で裏取り
- [x] Phase A 着手判定 (本 plan に GO / pivot / 撤退)

### Done 条件

- 「Mathlib に Slepian–Wolf converse は無い」を裏取り済み (loogle + rg)
- side info Fano が paired conditioner で書ける見込みを inventory で確認 (新規補題不要を裏取り)
- Phase A skeleton (`InformationTheory/Shannon/SlepianWolf.lean` の sorry-driven 出だし) が書ける状態

### 工数感

1 ターン (10〜15 分)。loogle + rg + 既存ファイル目視。

### 結果 (2026-05-10)

成果物 `slepian-wolf-mathlib-inventory.md`。要点:

- (a) **Mathlib に Slepian–Wolf 不在** (loogle 0 件)
- (b) **side info Fano は paired conditioner で出る** — 既存 `fano_inequality_measure_theoretic` の `Yo` 型が「任意の `MeasurableSpace`」なので `Y × S` で呼べる。Phase A wrapper は ~15 行
- (c) chain rule (`entropy_pair_eq_entropy_add_condEntropy`) + conditioning monotonicity (`condEntropy_le_condEntropy_of_pair`) は `InformationTheory/Shannon/Entropy.lean` 既存
- (d) 任意 μ の `entropy μ Xs ≤ log (Fintype.card α)` は **Mathlib・InformationTheory 両方に不在**、Phase A で新規 (~30〜50 行、Gibbs 不等式 / `klDiv_nonneg` 経由)
- (e) ペア plumbing は `Measurable.prodMk` + `Fintype.card_prod` で完備、新規ゼロ

工数見立て: **2 週間以内 / 280〜450 行**。シード見積「2〜3 週間 / 400〜600 行」より下方修正。

---

## Phase A - side info Fano wrapper + `entropy_le_log_card` 📋

### スコープ

```lean
namespace InformationTheory.Shannon

/-- 任意 μ 上の `H(W) ≤ log (Fintype.card α)`。Gibbs の不等式 (= `klDiv_nonneg`) から導出。 -/
theorem entropy_le_log_card
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → α) (hXs : Measurable Xs) :
    entropy μ Xs ≤ Real.log (Fintype.card α)

end InformationTheory.Shannon

namespace InformationTheory.MeasureFano

/-- side info 入り Fano: `Yo` を `(Yo, sideInfo) : Ω → Y × S` 形に paired し、既存
`fano_inequality_measure_theoretic` をそのまま呼ぶ thin wrapper。 -/
theorem fano_inequality_with_side_info
    {Ω : Type*} [MeasurableSpace Ω]
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
      [MeasurableSpace X] [MeasurableSingletonClass X]
    {Y S : Type*} [MeasurableSpace Y] [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Si : Ω → S)
    (decoder : Y × S → X)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hSi : Measurable Si)
    (hdec : Measurable decoder)
    (hcard : 2 ≤ Fintype.card X) :
    condEntropy μ Xs (fun ω => (Yo ω, Si ω)) ≤
      Real.binEntropy
        (errorProb μ Xs (fun ω => (Yo ω, Si ω)) decoder)
        + errorProb μ Xs (fun ω => (Yo ω, Si ω)) decoder
            * Real.log ((Fintype.card X : ℝ) - 1)

end InformationTheory.MeasureFano
```

### Steps

- [ ] `InformationTheory/Shannon/SlepianWolf.lean` を新設 (skeleton + 2 主補題 = sorry)
- [ ] `entropy_le_log_card` の証明
  - [ ] uniform measure `(Fintype.card α : ℝ≥0∞)⁻¹ • Measure.count` を target ν として `klDiv (μ.map Xs) ν ≥ 0` を `klDiv_nonneg` で取得
  - [ ] `klDiv_discrete_toReal_eq_sum` (`InformationTheory/Shannon/Bridge.lean`) で展開し `entropy μ Xs - log (Fintype.card α) ≤ 0` に整形
  - [ ] AC 仮定 `(μ.map Xs) ≪ (Fintype.card α)⁻¹ • Measure.count` を「uniform は full support」から自動 derive
- [ ] `fano_inequality_with_side_info` の証明
  - [ ] `Yo' := fun ω => (Yo ω, Si ω) : Ω → Y × S` の measurability を `Measurable.prodMk` で 1 行
  - [ ] 既存 `fano_inequality_measure_theoretic μ Xs Yo' decoder` を直接呼ぶ
- [ ] `InformationTheory.lean` に `import InformationTheory.Shannon.SlepianWolf` 追記
- [ ] `lake env lean InformationTheory/Shannon/SlepianWolf.lean` silent

### Done 条件

- 上記 2 補題が silent
- `InformationTheory.lean` に import 追記済
- skeleton-driven で `entropy_le_log_card` → `fano_inequality_with_side_info` の順に sorry を割る

### 工数感

**1〜2 セッション (~80〜120 行)**。`fano_inequality_with_side_info` は wrapper のみ ~15 行、`entropy_le_log_card` は klDiv_nonneg 経由で ~30〜50 行。残りは import / namespace open / docstring。

### リスク / 撤退ライン

- **`klDiv (μ.map Xs) (uniform on α)` の AC 自動 derive で詰まる** 場合 → uniform を `Measure.count` の単純 scalar 倍で書き直し、`Measure.count` の AC は singleton 質量からの逆算で手動証明 (~20 行追加)
- **Loomis–Whitney の `entropy_le_log_image_card` と統合する選択肢** — Loomis–Whitney は `image f` の濃度版なので一般化親としては自然だが、Phase A では時間優先で **uniform 仮定を外した別補題** として立てる方針 (将来 refactor で統合候補)

---

## Phase B - 3 bound (X / Y / sum) の本体実装 📋

### スコープ

```lean
namespace InformationTheory.Shannon

/-- Slepian–Wolf converse, X bound: `log Mx ≥ H(X|Y) - δ(Pe)`. -/
theorem slepian_wolf_converse_X
    {Ω : Type*} [MeasurableSpace Ω]
    {α β : Type*}
      [Fintype α] [DecidableEq α] [Nonempty α]
        [MeasurableSpace α] [MeasurableSingletonClass α]
      [Fintype β] [DecidableEq β] [Nonempty β]
        [MeasurableSpace β] [MeasurableSingletonClass β]
    {Mx My : ℕ} [NeZero Mx] [NeZero My]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → α) (Ys : Ω → β)
    (eX : α → Fin Mx) (eY : β → Fin My)
    (dec : Fin Mx × Fin My → α × β)
    (hXs : Measurable Xs) (hYs : Measurable Ys)
    (hcard : 2 ≤ Fintype.card (α × β))
    -- (eX, eY, dec) はすべて Fintype 上 → 自動 measurable で hypothesis 不要見込み
    : Real.log (Mx : ℝ) ≥
        InformationTheory.MeasureFano.condEntropy μ Xs Ys
          - Real.binEntropy
              (InformationTheory.MeasureFano.errorProb μ
                (fun ω => (Xs ω, Ys ω))
                (fun ω => (eX (Xs ω), eY (Ys ω)))
                dec)
          - InformationTheory.MeasureFano.errorProb μ
              (fun ω => (Xs ω, Ys ω))
              (fun ω => (eX (Xs ω), eY (Ys ω)))
              dec
            * Real.log ((Fintype.card (α × β) : ℝ) - 1)

/-- Slepian–Wolf converse, Y bound: `log My ≥ H(Y|X) - δ(Pe)`. (X / Y 対称) -/
theorem slepian_wolf_converse_Y …
  -- 上記の X / Y を swap した形

/-- Slepian–Wolf converse, sum bound: `log Mx + log My ≥ H(X, Y) - δ(Pe)`. -/
theorem slepian_wolf_converse_sum …

end InformationTheory.Shannon
```

### 証明骨格 (X bound、4 段 calc)

```
log Mx
  ≥ entropy μ (eX ∘ Xs)                                    -- Phase A: entropy_le_log_card
                                                              (eX∘Xs : Ω → Fin Mx, Fintype.card (Fin Mx) = Mx)
  ≥ condEntropy μ (eX ∘ Xs) Ys                             -- 「H(W) ≥ H(W|Y)」 (conditioning reduces entropy)
                                                              = mutualInfo_eq_entropy_sub_condEntropy + mutualInfo_nonneg
  = condEntropy μ (eX∘Xs, Xs) Ys - condEntropy μ Xs (eX∘Xs, Ys)
                                                              -- 条件付き chain rule
                                                              -- H(eX∘Xs | Y) = H(eX∘Xs, Xs | Y) - H(Xs | eX∘Xs, Y)
                                                              -- (Phase B-3 の山場、要素材確認)
  ≥ condEntropy μ Xs Ys - condEntropy μ Xs (eX∘Xs, Ys)     -- H(eX∘Xs, Xs | Y) ≥ H(Xs | Y)
                                                              (pair の方が情報多い → cond entropy 大きい)
  ≥ condEntropy μ Xs Ys - δ(Pe)                             -- Phase A: fano_inequality_with_side_info
                                                              -- conditioner = (eX∘Xs, Ys)、decoder' : Fin Mx × β → α
                                                              -- decoder' (m_x, y) = Prod.fst (dec (m_x, eY y))
                                                              -- Pe' = μ{Xs ≠ decoder'(eX∘Xs, Ys)} ≤ Pe (joint error → marginal error)
                                                              -- (binEntropy / 線形項は Pe'/Pe について単調なので Pe で押さえる)
```

(`δ(Pe) := Real.binEntropy Pe + Pe · Real.log (|α × β| - 1)`)

注意点 (Phase B 着手時の判断ログ候補):
- 最後の Fano 適用での **decoder 構成**: 「`Ys` から `eY(Ys)` を計算 → `dec` を呼ぶ → `Prod.fst` で X 成分を取る」が自然。Pe (joint) は Pe' (marginal X error) より大きい / 等しい (joint error 事象 ⊇ marginal error 事象) ので、Fano の上界も joint Pe で書ける。**ただし binEntropy は単調ではない** (Pe ∈ [0, 1/2] で増、[1/2, 1] で減) ため、Pe ≤ 1/2 の領域に restrict するか、`Real.binEntropy_le_log_two` で粗く押さえるか、別 wrapper で書き直すかを Phase B-Step 4 で判断
- 簡易ルート: **alphabet を `α × β` (joint source) として Fano を 1 回呼び、3 bound 全部を joint conditioner `(eX∘Xs, eY∘Ys)` から派生する**。これなら Pe / decoder は 3 bound 共通、`Real.binEntropy` の単調性問題も Pe 1 個に集約。ただし「marginal error が joint error より大きいわけがない」という観察に依拠

### Steps

- [ ] X bound 主定理 `slepian_wolf_converse_X` の skeleton (`:= by sorry`)
- [ ] (X bound) Step 1: `log Mx ≥ entropy μ (eX ∘ Xs)` ─ Phase A の `entropy_le_log_card` を 1 回呼ぶ
- [ ] (X bound) Step 2: `entropy μ (eX∘Xs) ≥ condEntropy μ (eX∘Xs) Ys` ─ 「H(W) ≥ H(W|Y)」を `mutualInfo_eq_entropy_sub_condEntropy` + `mutualInfo_nonneg` で示す helper を Phase B 内に立てる (~10 行)
- [ ] (X bound) Step 3: chain rule で `condEntropy μ (eX∘Xs) Ys = entropy μ (eX∘Xs, Xs | Ys) - ...` に展開 ─ 既存 `entropy_pair_eq_entropy_add_condEntropy` の **条件付き版** が必要。**Phase B-3 の山場**: 条件付き chain rule (`H(X, Z | Y) = H(Z | Y) + H(X | Y, Z)`) が `InformationTheory/Shannon/CondMutualInfo.lean` の `mutualInfo_chain_rule` と関連、要確認 (新規補題 ~50 行になる可能性)
- [ ] (X bound) Step 4: `entropy μ (eX∘Xs, Xs | Ys) ≥ condEntropy μ Xs Ys` ─ 「より大きい RV の条件付き entropy はより大きい」、`entropy_pair_eq_entropy_add_condEntropy` + `condEntropy_nonneg` で導出
- [ ] (X bound) Step 5: `condEntropy μ Xs (eX∘Xs, Ys) ≤ condEntropy μ Xs Ys` の代わりに、conditioner 増やしの正しい向き `condEntropy μ Xs (eX∘Xs, eY∘Ys, Ys) ≤ condEntropy μ Xs (eY∘Ys, Ys)` を使い、Phase A `fano_inequality_with_side_info` で `≤ δ(Pe)` に押さえる
- [ ] (Y bound) `slepian_wolf_converse_Y` ─ X / Y 対称、X bound を **swap した argument permutation で写経 ~30 行**
- [ ] (sum bound) `slepian_wolf_converse_sum` ─ `H(X, Y) = H(X) + H(Y|X)` (chain rule) を分解し、X bound + Y bound を組み合わせる **か**、または `entropy μ (eX∘Xs, eY∘Ys) ≤ log (Mx · My)` から直接派生 (どちらが安いかは Phase B 着手時に判断)
- [ ] 各 bound の `lake env lean` silent

### Done 条件

- 3 bound すべて silent
- 共通 helper (`entropy_ge_condEntropy` など) はファイル末尾に格納
- `errorProb` は 3 bound で同じ表式 (decoder = `dec`、conditioner = `(eX∘Xs, eY∘Ys)`)

### 工数感

**2〜3 セッション (~150〜250 行)**:

- X bound: 80〜120 行 (5 段 calc + 条件付き chain rule helper)
- Y bound: 30 行 (写経 + 引数 swap)
- sum bound: 50〜80 行 (chain rule 経由)
- 共通 helper: ~20〜30 行

### リスク / 撤退ライン

- **Step 3 (条件付き chain rule) で「自分で書くしかない」と判明し 100 行を超える**場合 → X bound の派生を別ルートに切り替え (e.g. `mutualInfo_chain_rule` を `(eX∘Xs, Xs)` で 1 回呼ぶ形) + proof-log で詳細記録
- **3 bound のうち 1 本でも 1 セッションで終わらない**場合 → そこで Phase B を打ち切り、X bound 単独で Phase C に進む。Y / sum は publish 後の followup
- **`hcard : 2 ≤ Fintype.card (α × β)` の `α × β` 整合で Fano 適用が型推論で詰まる**場合 → 個別 `α` `β` の `2 ≤ Fintype.card α` `2 ≤ Fintype.card β` 仮定に書き換え (Fano を per-axis に呼ぶ形)

---

## Phase C - 3 bound 統合 + publish 形整理 🌙

### スコープ

```lean
namespace InformationTheory.Shannon

/-- Slepian–Wolf converse (single-shot, 3 bound 統合形). -/
theorem slepian_wolf_converse_single_shot
    {Ω : Type*} [MeasurableSpace Ω]
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
      [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    {Mx My : ℕ} [NeZero Mx] [NeZero My]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → α) (Ys : Ω → β)
    (eX : α → Fin Mx) (eY : β → Fin My)
    (dec : Fin Mx × Fin My → α × β)
    (hXs : Measurable Xs) (hYs : Measurable Ys)
    (hcard : 2 ≤ Fintype.card (α × β)) :
      -- 3 bound を `And.intro` で接続するか、構造体化するか
      (Real.log (Mx : ℝ) ≥ condEntropy μ Xs Ys - δ(Pe))
      ∧ (Real.log (My : ℝ) ≥ condEntropy μ Ys Xs - δ(Pe))
      ∧ (Real.log (Mx : ℝ) + Real.log (My : ℝ)
           ≥ entropy μ (fun ω => (Xs ω, Ys ω)) - δ(Pe))

end InformationTheory.Shannon
```

### Steps

- [ ] 3 bound 統合判断: `And.intro × 2` で 3 つ tuple 化 vs 構造体 `SlepianWolfConverse` 新設 vs **3 別 theorem のまま** で打ち止め、のいずれか
  - 推奨: **3 別 theorem 維持 + 統合 `slepian_wolf_converse_single_shot` を別 wrapper として追加**。利用側からは個別 / 統合の両方が見える
- [ ] `δ(Pe)` を文字定義 (Phase B では inline) に切り替えるか判断
  - 推奨: **inline 維持**。`shannon_converse_single_shot` も `δ` 関数を立てていない先例
- [ ] publish 形 docstring 整備 (Cover–Thomas 15.4 への参照、ベース定理の説明)
- [ ] `slepian_wolf_converse_single_shot` 統合定理の証明 (3 個別定理を `⟨h1, h2, h3⟩` で組む形、~10 行)
- [ ] `lake env lean InformationTheory/Shannon/SlepianWolf.lean` silent
- [ ] proof-log 取得 (`docs/proof-logs/proof-log-slepian-wolf.md` + metrics)

### Done 条件

- 統合定理 `slepian_wolf_converse_single_shot` が silent
- 3 個別定理 (X / Y / sum) も並行して silent
- proof-log + metrics 取得

### 工数感

1 セッション (~50〜80 行)。Phase B が片付けば組み合わせのみ。

### リスク / 撤退ライン

- **3 bound のうち 1〜2 本しか出ていない場合** → 出ている分だけで Phase C 統合形を書く + 残り bound は将来課題に。proof-log で詳細記録
- **`δ(Pe)` 定義の構造化で議論が長引く**場合 → inline 維持で確定、構造体化は別 refactor として切り出し

---

## 失敗判定 / 撤退ライン (全体)

- **Phase 0 で side info Fano が paired conditioner では出ないと判明**した場合 → Phase A の見積りが大幅増 (新規 Fano 補題 100〜150 行)、Phase B の plumbing も再見積もり必要。proof-log で記録 + 場合により計画破棄
- **Phase A の `entropy_le_log_card` で 100 行を超える**場合 → klDiv_nonneg ルートを諦め、`negMulLog` 凹性 + Jensen 直接ルートに switch (~50 行追加見込み)
- **Phase B で 3 bound のうち 1 本も書き上がらない**場合 → 計画全体を「side info Fano + entropy_le_log_card」だけの Phase A 単独で publish (= Slepian–Wolf 直接 publish ではなく「side info Fano プリミティブ整備」として切り出し)
- どのケースでも「Slepian–Wolf に届かなかった」ではなく **「distributed source coding 形式化での具体的な詰まりポイント」をデータとして残す**

---

## 当面の next step

1. ~~**Phase 0 (Mathlib + 既存 InformationTheory API インベントリ)**~~ ✅ 完 (2026-05-10)、`slepian-wolf-mathlib-inventory.md` 参照
2. **Phase A skeleton 作成** ← **次これ**
   - `InformationTheory/Shannon/SlepianWolf.lean` 新設
   - `entropy_le_log_card` + `fano_inequality_with_side_info` の 2 sorry 出だし
   - `InformationTheory.lean` に import 追記
3. **Phase A の 2 sorry 充填**
4. **Phase B X bound 着手**
5. **Phase B Y / sum bound + Phase C 統合**

---

## 参照

- 親 seed: [`docs/moonshot-seeds.md`](../moonshot-seeds.md) Seed 3
- 兄弟 plan:
  - [Shannon moonshot (single-shot converse)](shannon-moonshot-plan.md)
  - [Shannon encoder extensions (Phase 4-δ)](shannon-encoder-extensions-plan.md)
  - [Loomis–Whitney moonshot](loomis-whitney-moonshot-plan.md)
- 既存実装:
  - `InformationTheory/Shannon/Converse.lean:81` `shannon_converse_single_shot`
  - `InformationTheory/Fano/Measure.lean:224` `fano_inequality_measure_theoretic`
  - `InformationTheory/Shannon/Entropy.lean:41` `entropy_pair_eq_entropy_add_condEntropy`
  - `InformationTheory/Shannon/Entropy.lean:240` `condEntropy_le_condEntropy_of_pair`
- M0 inventory: [`slepian-wolf-mathlib-inventory.md`](slepian-wolf-mathlib-inventory.md)

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-10: Phase B X bound 派生ルートを `condMutualInfo` 経由にピボット

**当初の派生** (Approach §「3 bound 共通の Cover–Thomas 派生 chain」):

```
log Mx ≥ H(eX∘Xs)
       ≥ H(eX∘Xs | Ys)
       = H(eX∘Xs, Xs | Ys) - H(Xs | eX∘Xs, Ys)        -- 条件付き chain rule (Phase B-3 の山場)
       ≥ H(Xs | Ys) - H(Xs | eX∘Xs, Ys)
       ≥ H(Xs | Ys) - δ(Pe)
```

**問題**: 「条件付き chain rule」 `H(X, Z | Y) = H(Z | Y) + H(X | Y, Z)` が `InformationTheory/Shannon/Entropy.lean` に未整備、新規補題 ~50 行になる。

**ピボット**: `condMutualInfo_eq_condEntropy_sub_condEntropy` + `condMutualInfo_comm` の 2 本既存補題で同等の派生を実現できることを発見。

```
H(X | Ys) - H(X | Ys, EX) = (condMI Xs EX Ys).toReal      -- bridge
                          = (condMI EX Xs Ys).toReal      -- comm
                          = H(EX | Ys) - H(EX | Ys, Xs)   -- bridge
                          ≤ H(EX | Ys)                    -- condEntropy_nonneg (新規 5 行)
                          ≤ H(EX) ≤ log Mx
```

**新規補題**: `condEntropy_nonneg` (5 行) のみ。条件付き chain rule (~50 行) 回避。
**結果**: X bound 60 行、Y bound 60 行 (X bound 写経)、sum bound 50 行。

### 2026-05-10: 側 info Fano wrapper の conditioner 順を `(Yo, Si)` に固定

`fano_inequality_with_side_info` で paired conditioner を `(Yo ω, Si ω)` の順とした。
利用側 (X bound) で `Yo := Ys, Si := EX` と渡し `(Ys, EX)` 順の conditioner を得る。
これで `condMutualInfo_eq_condEntropy_sub_condEntropy` の RHS `H(X | Ys, EX)` (≡ `condEntropy μ Xs (fun ω => (Ys ω, EX ω))`) と直接マッチし、prodComm 経由の swap (証明 ~30 行) を回避。

### 2026-05-10: Phase C 統合形 = 3 bound の `And` tuple

`slepian_wolf_converse_single_shot` を 3 bound の `⟨h_X, h_Y, h_sum⟩` で構成。各 bound は
それぞれ別の Pe (X bound = marginal X error、Y bound = marginal Y error、sum bound = joint
error) を抱えるため、構造体化せず `And` で素直に束ねる。`δ(Pe)` も inline 維持
(計画推奨方針)。


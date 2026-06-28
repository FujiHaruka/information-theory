# Relay cut-set: headline assembly (operational layer) サブ計画

> **Parent**: [`relay-cutset-moonshot-plan.md`](relay-cutset-moonshot-plan.md) §「残 = headline assembly (operational 層, 次 leg)」

## 進捗 — ✅ CLOSED (2026-06-29)

**`relay_cutset_outer_bound` genuine closure 達成** (sorryAx-free + 独立 honesty audit `@audit:ok`)。BC-cut の当初 **wall-likely 判定は gateway-atom-first で覆った** (= tractable, not wall): per-letter causal telescoping は既存資産 `mutualInfo_le_of_postprocess` + `jointEntropy_chain_rule` + `isMarkovChain_comp_conditioner_right` で組め、d-separation 自作機構 (~150-250 行見積り) は不要だった。`relay_broadcast_cut_singleletterize` (block 条件付き MI) は予測通り headline では未使用 (telescoping が直接 per-letter sum を出す)。

- [x] M0 — verbatim API 確認 ✅
- [x] Phase 2 — MAC-cut genuine closure (`relay_mac_cut_outer_bound`, commit `be67233f`) ✅
- [x] Phase 3 — BC-cut gateway atom (`relay_broadcast_cut_message_telescope`, commit `786b15e2`, wall-likely 覆る) + combined headline (`relay_broadcast_cut_outer_bound` + `relay_cutset_outer_bound`, commit `f2547c93`, `@audit:ok` commit `9b4de42d`) ✅

成果 (`InformationTheory/Shannon/RelayCutset.lean`, 全 `@audit:ok`・0/0/0 sorryAx-free): 2 single-letterization (leg 3) + `relay_mac_cut_outer_bound` + `relay_broadcast_cut_message_telescope` + `relay_broadcast_cut_outer_bound` + `relay_cutset_outer_bound`。撤退ライン (BC sorry+@residual / user-decision 停止) は **不発** (BC genuine 閉)。以下は設計史 (参照用、再作業不要)。

## ゴール / Approach

`InformationTheory/Shannon/RelayCutset.lean` に operational headline
`relay_cutset_outer_bound : Real.log (M:ℝ) ≤ relayCutsetBound Ib Im` (= `min Ib Im`) を追加する。
DONE 資産 (構造定義 + 2 本の single-letterization, `@audit:ok`) に乗せ、雛形は Line A
`bc_converse` (message-level Fano を single-letterization と `.mono`/`le_min` で合成)。

**全体の形**: 単一メッセージ `W` + 単一 destination なので
1. **destination Fano** (`shannon_converse_single_shot`): `log M ≤ I(W;Yⁿ).toReal + Fano`。
2. **2 cut で `I(W;Yⁿ)` を分岐**:
   - **MAC-cut (易, genuine)**: `I(W;Yⁿ) ≤ I(Xⁿ,X₁ⁿ;Yⁿ)` (`mutualInfo_le_of_markov`, block Markov
     precondition) → `relay_mac_cut_singleletterize` で `≤ ∑ᵢ I(Xᵢ,X₁ᵢ;Yᵢ)`。よって `log M ≤ Im`。
   - **BC-cut (核, wall-likely)**: `I(W;Yⁿ) ≤ ∑ᵢ I(Xᵢ;Y₁ᵢ,Yᵢ|X₁ᵢ)` の橋渡しが **既存
     `relay_broadcast_cut_singleletterize` (block 条件付き MI) を直接消費できない** (下記
     §BC-cut 壁判定)。gateway atom = message→per-letter telescoping 補題を 1 本 dispatch し、
     通れば `log M ≤ Ib`。
3. **min 合成**: `le_min_iff.mpr ⟨log M ≤ Ib, log M ≤ Im⟩` → `log M ≤ relayCutsetBound Ib Im`。

scalar form の意図 (per-letter sum → `n·max_p` の外出し) を保つため、`Ib`/`Im` は per-letter
sum + Fano slack を上界する **externalisation 仮説** (regularity, not load-bearing) で受ける。
MAC-cut は genuine に閉じるので、まず `relay_mac_cut_outer_bound : log M ≤ Im` を 0 sorry で
publish し、combined `relay_cutset_outer_bound` は BC-cut の gateway atom 次第。

## BC-cut 壁判定 (本サブ計画の主成果)

**判定: wall-likely (in-project shortcut 不在 = genuine self-build ~150-250 行)。**
既存 `relay_broadcast_cut_singleletterize` (block `I(Xⁿ;Y₁ⁿ,Yⁿ|X₁ⁿ) ≤ ∑ᵢ ...`) は headline で
**直接使えない**。決定的根拠:

- MAC converse `mac_message_le_condMI` (`MultipleAccess/Converse.lean:378`) が **relay BC-cut
  と同型の message→block 条件付き MI 橋** `I(Msg₁;(Msg₂,Yⁿ)) ≤ I(X₁ⁿ;Yⁿ|X₂ⁿ)` を持つが、その
  Step 1 (`:394-401`) は `h_indep : mutualInfo μ Msg₁ Msg₂ = 0` を使って chain rule の
  `I(Msg₁;Msg₂)` 項を消し `I(Msg₁;(Msg₂,Yⁿ)) = I(Msg₁;Yⁿ|Msg₂)` に reduce している
  (**independence が load-bearing**)。
- relay には独立な第二メッセージが無い: 条件付け側 `X₁ⁿ` (relay 入力) は `X₁ᵢ = f(Y₁^{<i})`
  で **`W` に因果依存** → `I(W;X₁ⁿ) ≠ 0`。よって MAC の `h_indep` analog が **FALSE**。これを
  honest precondition (`W ⊥ X₁ⁿ`) として渡すのは `false-hypothesis` defect (tier 5) になる。
- block で素直に組むと chain rule `I(W;X₁ⁿ,Yⁿ,Y₁ⁿ) = I(W;X₁ⁿ) + I(W;Yⁿ,Y₁ⁿ|X₁ⁿ)` の余剰項
  `I(W;X₁ⁿ) ≠ 0` が残る (オーケストレーター障害仮説 = **確認**)。さらに `X₁ⁿ` は
  `(Yⁿ,Y₁ⁿ)` の決定的関数 (`H(X₁ⁿ|Yⁿ,Y₁ⁿ)=0`) なので `I(W;Yⁿ,Y₁ⁿ|X₁ⁿ) ≤ I(W;Yⁿ,Y₁ⁿ)`
  (条件付けが MI を **減らす** = 橋を逆向きにする)。よって block 条件付き MI 経由は閉じない。
- 退化境界での確認: `n=1` では `X₁₁ = relay 0 (空) = const` で `I(W;X₁ⁿ)=0` (独立成立) →
  block 橋が成立。余剰は `n≥2` (`X₁₂ = f(Y₁₁)` が `W` 依存) でのみ出る。statement は生きている
  (vacuous でない)。

**壁の正体 (plumbing でなく gap)**: CT 15.10.1 の cut-set 証明は block 条件付き MI を経由せず、
各 letter で causal conditioner `X₁ᵢ` を導入する per-letter telescoping
(`I(W;Yⁿ) ≤ ∑ᵢ I(W,Y^{<i},Y₁^{<i};Yᵢ,Y₁ᵢ|X₁ᵢ) ≤ ∑ᵢ I(Xᵢ;Yᵢ,Y₁ᵢ|X₁ᵢ)`) で余剰項を
telescoping 相殺する。この telescoping は in-project に資産が無い。

**壁判定メタデータ** (CLAUDE.md「壁判定 必須メタデータ」):
- 試したルート ≥2: (1) MAC `mac_message_le_condMI` 流用 → `h_indep` analog が FALSE で詰まる。
  (2) block post-processing + 条件付き DPI `condMutualInfo_le_of_markov_joint` → `I(W;X₁ⁿ)`
  余剰 + 条件付けが MI を減らす逆向きで詰まる。
- gateway atom: §gateway atom の `relay_broadcast_cut_message_telescope` (下記)。実装 dispatch
  = N (本計画 Phase 3 で初 dispatch)。**family 丸ごと壁宣言の前に atom を 1 本投げる**。
- 反証試行: `n=1` 退化で statement 成立 (上記)、`n≥2` で余剰顕在化。statement は生きている。
- plumbing vs gap: **gap** (per-letter causal telescoping の命題が Mathlib/in-project に不在)。
  既存 block single-letterization への配線ではない。
- self-build 行数: ~150-250 行 (chain rule over `Fin n` + causal conditioner 導入 + memoryless
  独立性 + telescoping 相殺)。template として最も近いのは `mac_message_le_condMI` (block 版, ~170
  行) だが independence で楽をしており、causal 版はそれより重い。
- loogle: telescoping 補題は MI-theory 固有で Mathlib 範囲外 (in-project def `condMutualInfo`)。
  in-project `rg` で relay message-telescope helper = 0 件確認済 (`mac` 系のみヒット)。

### gateway atom (Phase 3 で 1 本 dispatch、通れば BC-cut genuine closure)

```lean
/-- BC-cut の message→per-letter telescoping (relay 因果構造を honest precondition 化)。
gateway atom: これが通れば BC-cut は genuine closure、通らねば wall。 -/
theorem relay_broadcast_cut_message_telescope
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Fin M)
    (Xs : Fin n → Ω → α) (X₁s : Fin n → Ω → α₁)
    (Ys : Fin n → Ω → β) (Y₁s : Fin n → Ω → β₁)
    (c : RelayCode M n α α₁ β β₁)
    (hW : Measurable W)
    (hXs : ∀ i, Measurable (Xs i)) (hX₁s : ∀ i, Measurable (X₁s i))
    (hYs : ∀ i, Measurable (Ys i)) (hY₁s : ∀ i, Measurable (Y₁s i))
    -- (A) 因果性 (honest, 構造的; NOT W⊥X₁ⁿ): relay 入力は過去 relay 観測の決定的関数
    (h_causal : ∀ i, X₁s i =
      fun ω ↦ c.relay i (fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
    -- (B) 無記憶性 (regularity)
    (h_memo : IsMemorylessChannel μ
      (fun i ω ↦ (Xs i ω, X₁s i ω)) (fun i ω ↦ (Y₁s i ω, Ys i ω))) :
    (mutualInfo μ W (fun ω j ↦ Ys j ω)).toReal
      ≤ ∑ i : Fin n,
          (condMutualInfo μ (Xs i) (fun ω ↦ (Y₁s i ω, Ys i ω)) (X₁s i)).toReal
```

- precondition (A) は relay code の `relay` field を使った honest な構造方程式 (regularity)。
  実装者は σ(Y₁^{<i})-可測性の弱形に置換してよいが、**`W ⊥ X₁ⁿ` の独立性に退化させてはならない**
  (それは false-hypothesis defect)。`mutualInfo μ W (fun ω↦X₁s _) = 0` 系の仮説を入れたら監査が
  tier 5 で弾く。
- 結論の per-letter 形は `relay_broadcast_cut_singleletterize` の RHS と一致 (同 file:110-112)。
  よって gateway atom が通れば、後段で `relay_broadcast_cut_singleletterize` を **使わず** に
  (telescoping が直接 per-letter sum を出すため) BC branch が閉じる。

## M0 — verbatim API 確認 📋

proof-log: **no** (在庫確認のみ)。下記 5 補題の verbatim シグネチャを実物 Read で確定済
(本計画起草時に確認、配線時に再 Read で型整合)。

1. **destination Fano** — `shannon_converse_single_shot`
   (`InformationTheory/Shannon/Converse.lean:70`):
   ```
   (μ)[IsProbabilityMeasure μ](Msg:Ω→M)(Yo:Ω→Y)(decoder:Y→M)
   (hMsg)(hYo)(hdecoder)
   (hMsg_uniform : μ.map Msg = (Fintype.card M:ℝ≥0∞)⁻¹ • Measure.count)
   (hcard : 2 ≤ Fintype.card M)(hMI_finite : mutualInfo μ Msg Yo ≠ ∞) :
   Real.log (Fintype.card M) ≤ (mutualInfo μ Msg Yo).toReal
     + Real.binEntropy (MeasureFano.errorProb μ Msg Yo decoder)
     + MeasureFano.errorProb μ Msg Yo decoder * Real.log ((Fintype.card M:ℝ) - 1)
   ```
   型クラス (section var): `{M}[Fintype M][DecidableEq M][Nonempty M][MeasurableSpace M]
   [MeasurableSingletonClass M]`, `{Y}[MeasurableSpace Y]`。**SBS 不要**。`Msg:=W`, `Y:=Fin n→β`,
   `Yo := fun ω j ↦ Ys j ω`。`Fintype.card (Fin M) = M` で `log M` 直書き。これが message-level
   Fano の入口 (chain-rule なし)。markov_encoder 版 (`:128`) は `I(encoder∘Msg;Yo)` を返すが、
   relay の `(Xⁿ,X₁ⁿ)` は `W` の決定的関数でないため **使わない** (base 版を使う)。

2. **MAC DPI** — `mutualInfo_le_of_markov`
   (`InformationTheory/Shannon/CondMutualInfo.lean:356`):
   ```
   (μ)[SBS X][Ne X][SBS Y][Ne Y](Xs:Ω→X)(Zc:Ω→Z)(Yo:Ω→Y)(meas)
   (hmarkov : IsMarkovChain μ Xs Zc Yo) : mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo
   ```
   `Z` に SBS 不要。`Xs:=W`, `Zc:= fun ω j ↦ (Xs j ω, X₁s j ω)` (型 `Fin n→(α×α₁)`),
   `Yo:= fun ω j ↦ Ys j ω`。

3. **MAC single-letterization** — `relay_mac_cut_singleletterize`
   (`RelayCutset.lean:82`, `@audit:ok`): `I(Xⁿ,X₁ⁿ;Yⁿ).toReal ≤ ∑ᵢ I(Xᵢ,X₁ᵢ;Yᵢ).toReal`、
   precondition `h_memo : IsMemorylessChannel μ (fun i ω↦(Xs i ω,X₁s i ω)) Ys`。block 入力形
   `fun ω j ↦ (Xs j ω, X₁s j ω)` は asset 2 の `Zc` と一致 (reindex 不要)。

4. **MI 有限性** — `mutualInfo_ne_top` (`InformationTheory/Shannon/MutualInfo.lean:174`):
   `[Fintype X][Fintype Y]` で `mutualInfo μ Xs Yo ≠ ∞`。`Fin n→(α×α₁)` / `Fin n→β` は Fintype
   (Pi finite) なので block MI 有限 → asset 2 の `.toReal` mono に使用。

5. **BC single-letterization** — `relay_broadcast_cut_singleletterize`
   (`RelayCutset.lean:103`, `@audit:ok`): block `I(Xⁿ;Y₁ⁿ,Yⁿ|X₁ⁿ).toReal ≤ ∑ᵢ
   I(Xᵢ;Y₁ᵢ,Yᵢ|X₁ᵢ).toReal`。**BC-cut では headline から直接消費不可** (§壁判定)。gateway atom が
   wall の場合のみ「per-letter sum まで来た後」の参照候補だが、telescoping が直接 per-letter sum を
   出すため最終的に未使用の見込み。

(条件付き DPI `condMutualInfo_le_of_markov_joint` (`ConverseMemorylessChainRule.lean:113`) は
MAC `mac_message_le_condMI` の Step 2 で使われる block 橋の部品。relay では block 橋自体が
余剰項で閉じないため headline では使わない。gateway atom の telescoping 内部で部分的に再利用しうる。)

## Phase 1 — headline skeleton + destination Fano 配線 📋

proof-log: **no** (skeleton)。

- [ ] `relay_mac_cut_outer_bound` と `relay_cutset_outer_bound` の 2 signature を `:= by sorry` で
      skeleton 化、型整合を `lake env lean` で確認 (sorry warning のみ)。
- [ ] 両 headline の冒頭 `Fano` abbrev: `Pe := MeasureFano.errorProb μ W (fun ω j↦Ys j ω) decoder`,
      `Fano := Real.binEntropy Pe + Pe * Real.log ((M:ℝ)-1)`。
- [ ] destination Fano (`shannon_converse_single_shot`) を両 headline に配線:
      `log M ≤ (mutualInfo μ W (fun ω j↦Ys j ω)).toReal + Fano`。`hMI_finite` は `mutualInfo_ne_top`。

### headline 候補シグネチャ (両者)

`relay_cutset_outer_bound` (combined):

```lean
theorem relay_cutset_outer_bound {Ω α α₁ β β₁ : Type*} [MeasurableSpace Ω]
    [Fintype α][DecidableEq α][Nonempty α][MeasurableSpace α]
      [MeasurableSingletonClass α][StandardBorelSpace α]
    [Fintype α₁][DecidableEq α₁][Nonempty α₁][MeasurableSpace α₁]
      [MeasurableSingletonClass α₁][StandardBorelSpace α₁]
    [Fintype β][DecidableEq β][Nonempty β][MeasurableSpace β]
      [MeasurableSingletonClass β][StandardBorelSpace β]
    [Fintype β₁][DecidableEq β₁][Nonempty β₁][MeasurableSpace β₁]
      [MeasurableSingletonClass β₁][StandardBorelSpace β₁]
    {M n : ℕ} [NeZero M]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Fin M)
    (Xs : Fin n → Ω → α) (X₁s : Fin n → Ω → α₁)
    (Ys : Fin n → Ω → β) (Y₁s : Fin n → Ω → β₁)
    (c : RelayCode M n α α₁ β β₁)
    (decoder : (Fin n → β) → Fin M)
    (hW : Measurable W)
    (hXs : ∀ i, Measurable (Xs i)) (hX₁s : ∀ i, Measurable (X₁s i))
    (hYs : ∀ i, Measurable (Ys i)) (hY₁s : ∀ i, Measurable (Y₁s i))
    (hdecoder : Measurable decoder)
    (hW_uniform : μ.map W = (Fintype.card (Fin M):ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ M)
    -- MAC-cut preconditions (regularity; genuine, not load-bearing):
    (h_markov_mac : IsMarkovChain μ W
      (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω))
    (h_memo_mac : IsMemorylessChannel μ (fun i ω ↦ (Xs i ω, X₁s i ω)) Ys)
    -- BC-cut preconditions (causal relay structure + memoryless; NOT W⊥X₁ⁿ):
    (h_causal : ∀ i, X₁s i =
      fun ω ↦ c.relay i (fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
    (h_memo_bc : IsMemorylessChannel μ
      (fun i ω ↦ (Xs i ω, X₁s i ω)) (fun i ω ↦ (Y₁s i ω, Ys i ω)))
    -- scalar-form externalisation of the per-letter max (regularity, NOT load-bearing):
    (Ib Im : ℝ)
    (h_bc_ext  : (∑ i : Fin n,
        (condMutualInfo μ (Xs i) (fun ω ↦ (Y₁s i ω, Ys i ω)) (X₁s i)).toReal)
        + Real.binEntropy (MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) decoder)
        + MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) decoder * Real.log ((M:ℝ)-1) ≤ Ib)
    (h_mac_ext : (∑ i : Fin n,
        (mutualInfo μ (fun ω ↦ (Xs i ω, X₁s i ω)) (Ys i)).toReal)
        + Real.binEntropy (MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) decoder)
        + MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) decoder * Real.log ((M:ℝ)-1) ≤ Im) :
    Real.log (M:ℝ) ≤ relayCutsetBound Ib Im
```

- `Ib` = broadcast-cut: per-letter sum `∑ᵢ I(Xᵢ;Y₁ᵢ,Yᵢ|X₁ᵢ).toReal` + Fano slack。
- `Im` = MAC-cut: per-letter sum `∑ᵢ I(Xᵢ,X₁ᵢ;Yᵢ).toReal` + Fano slack。
- `h_bc_ext`/`h_mac_ext` は「`Ib`/`Im` が per-letter sum + Fano を上界」という外出し
  (textbook の `max_p × n` を呼び出し側へ; scalar form の既存意図)。**core は branch で genuine に
  証明されるため load-bearing でない** (監査の sufficiency check 通過見込み)。
- 引数順: def は `relayCutsetBound (Ib Im) := min Ib Im` (Ib=broadcast slot)。親の本文表記
  `relayCutsetBound Im Ib` は min 対称ゆえ値同値だが、slot 意味を def と揃え `Ib Im` を採用。
- **代替形 (より honest, Ib/Im 外出し無し)**: 結論を `relayCutsetBound (∑ᵢ condMI.. + Fano)
  (∑ᵢ MI.. + Fano)` の concrete 形にして `Ib Im`/`h_*_ext` を削る。`max_p` 読みは失うが abstract
  slot ゼロ。orchestrator の「Ib/Im 明示」要求に応えるため primary は abstract 形を推奨、本形は
  variant として記録。

`relay_mac_cut_outer_bound` は上記から BC-cut 系の引数 (`Y₁s`, `c`, `h_causal`, `h_memo_bc`,
`Ib`, `h_bc_ext`) を落とし、結論を `Real.log (M:ℝ) ≤ Im` にした genuine 版。

## Phase 2 — MAC-cut genuine closure 📋

proof-log: **yes** (operational step、雛形 `bc_singleletterize_bound₁` 相当)。
deliverable: `relay_mac_cut_outer_bound : Real.log (M:ℝ) ≤ Im` を **0 sorry** で publish。

operational step の補題分解 (1 本に inline でも可):

- [ ] **step1 (Fano)**: `shannon_converse_single_shot μ W (fun ω j↦Ys j ω) decoder ...` で
      `log M ≤ I(W;Yⁿ).toReal + Fano`。`hMI_finite := mutualInfo_ne_top ...`。
- [ ] **step2 (MAC DPI)**: `mutualInfo_le_of_markov μ W (fun ω j↦(Xs j ω,X₁s j ω))
      (fun ω j↦Ys j ω) ... h_markov_mac` で `I(W;Yⁿ) ≤ I(Xⁿ,X₁ⁿ;Yⁿ)` (ℝ≥0∞)。
      `ENNReal.toReal_mono (mutualInfo_ne_top ..)` で `.toReal` 化。
- [ ] **step3 (single-letterize)**: `relay_mac_cut_singleletterize μ Xs X₁s Ys hXs hX₁s hYs
      h_memo_mac` で `I(Xⁿ,X₁ⁿ;Yⁿ).toReal ≤ ∑ᵢ I(Xᵢ,X₁ᵢ;Yᵢ).toReal`。
- [ ] **合成**: `step1.trans (by linarith [step2, step3])` 系で
      `log M ≤ ∑ᵢ I(Xᵢ,X₁ᵢ;Yᵢ).toReal + Fano`、`h_mac_ext` で `≤ Im`。
- [ ] block 入力形整合の確認: step2 の `Zc = fun ω j↦(Xs j ω, X₁s j ω)` (型 `Fin n→(α×α₁)`) は
      step3 の入力と同一。**型 `(Fin n→α)×(Fin n→α₁)` には変換しない** (reindex 回避)。SBS
      instance: `Fin M` / `Fin n→β` は finite 由来で derive。

> independent honesty audit: Phase 2 で新 `sorry` は導入しない (0 sorry genuine) ため、本 Phase
> 単独では audit 不要。Phase 3 で BC sorry を導入する場合のみ orchestrator が `honesty-auditor`
> を 1 体起動 (combined headline を `InformationTheory.lean` に wire する前)。

## Phase 3 — BC-cut gateway atom dispatch + combined headline 📋

proof-log: **yes**。deliverable: combined `relay_cutset_outer_bound`。

- [ ] **gateway atom dispatch**: `relay_broadcast_cut_message_telescope` (§gateway atom) を
      `lean-implementer` に 1 本投げ、honest precondition (A 因果 + B memoryless) で通るか見る。
      **family 丸ごとの wall 確定の前に atom を実装する** (gateway-atom-first)。
- [ ] **(通った場合 = genuine closure)**: telescoping が `I(W;Yⁿ).toReal ≤ ∑ᵢ
      I(Xᵢ;Y₁ᵢ,Yᵢ|X₁ᵢ).toReal` を直接出すので、destination Fano と合成し `log M ≤ ∑ᵢ .. + Fano
      ≤ Ib` (`h_bc_ext`)。combined を `le_min_iff.mpr ⟨bc_final, mac_final⟩` で閉じ、0 sorry。
- [ ] **(通らなかった場合 = wall)**: 撤退ライン (下記) 発動。

### 撤退ライン (BC-cut が gateway atom で閉じなかった場合)

- BC branch の `I(W;Yⁿ).toReal ≤ ∑ᵢ I(Xᵢ;Y₁ᵢ,Yᵢ|X₁ᵢ).toReal` を **`sorry` +
  `@residual(plan:relay-cutset-headline-plan)`** で残す (この計画が gateway atom + telescoping の
  closure 設計の SoT)。`@residual` 配置は当該 `have` 直前行コメント (audit-tags.md「配置」)。
- **`relay_mac_cut_outer_bound : log M ≤ Im` は genuine (0 sorry) で先に publish** (`@audit:ok`
  候補)。これが MAC-cut 単独の honest 完成成果。
- combined `relay_cutset_outer_bound` は BC sorry を 1 個含む partial (type-check done) として
  commit、**user-decision で停止** (telescoping を本計画 Phase 3 続行で self-build するか、別
  closure plan `relay-broadcast-cut-telescope-plan` に分離するかを user に問う)。telescoping を
  別 plan に切り出す場合のみ residual を `@residual(plan:relay-broadcast-cut-telescope-plan)` に
  付け替え、同名 kebab plan を新規作成。
- **禁止**: BC-cut の核を `*Hypothesis`/`IsRelayBCClaim` 等の predicate に bundle して仮説で渡す
  (load-bearing hyp = honesty defect)。`W ⊥ X₁ⁿ` / `mutualInfo μ W X₁ⁿ = 0` 系の独立性仮説で
  telescoping を skip するのも false-hypothesis defect (relay では FALSE)。撤退は `sorry` のみ。
- orchestrator: BC `sorry` + `@residual` 導入の commit で `honesty-auditor` を 1 体起動
  (signature honest + residual class 正当 + load-bearing でないことを独立検証)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。決着済 entry は削除 (git が履歴)。

1. **2026-06-29 BC-cut 壁判定 (wall-likely, gateway-atom-pending)**: 既存
   `relay_broadcast_cut_singleletterize` (block 条件付き MI) は headline で直接消費不可。
   決定的根拠 = MAC `mac_message_le_condMI:394-401` の message→block 橋が `h_indep`
   (`I(Msg₁;Msg₂)=0`) load-bearing で、relay には独立第二メッセージが無く `I(W;X₁ⁿ)≠0`
   (causal feedback) ゆえ analog が FALSE。block 経由は chain-rule 余剰 `I(W;X₁ⁿ)` + 条件付けが
   MI を減らす逆向きで閉じない。CT 15.10.1 の per-letter causal telescoping (~150-250 行,
   in-project 資産無し) が必要。gateway atom `relay_broadcast_cut_message_telescope` を Phase 3 で
   dispatch し tractability を確定 (gateway-atom-first)。`cause:` タグは closure 時に付与
   (gap or 反証で over/under のいずれか)。
2. **2026-06-29 MAC-cut genuine + 単独 publish 方針**: MAC-cut は `shannon_converse_single_shot`
   + `mutualInfo_le_of_markov` + `relay_mac_cut_singleletterize` で素直に閉じるため、
   `relay_mac_cut_outer_bound : log M ≤ Im` を 0 sorry の独立 headline として先に publish。
   combined は BC gateway atom 次第。
3. **2026-06-29 message-level Fano は base `shannon_converse_single_shot` を採用**: markov_encoder
   版 (`Converse.lean:128`) は `I(encoder∘Msg;Yo)` を返すが relay の `(Xⁿ,X₁ⁿ)` は `W` の決定的
   関数でない (relay 入力が確率的に Y₁ 依存) ため不適。base 版 (`:70`, SBS 不要) で `I(W;Yⁿ)` を
   直接受け、DPI は MAC-cut 側の Markov で別途。

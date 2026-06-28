# MAC (Multiple Access Channel) Capacity Region — genuine-closure ムーンショット計画 🌙

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §Ch.15 (Network IT / DSC mini-chapter)
> **Inventory**: [`mac-inventory.md`](mac-inventory.md) (§A in-project 流用 / §B Mathlib / §C 削除済 scaffold 型 / §D gap)

> **Status**: **converse genuine-closed** (Phase 0 / A1 / A2 ✅、achievability 残)。**目標 = Cover–Thomas 2nd ed. Theorem 15.3.1 (2-user DMC capacity region) を標準B (proof done = 0 sorry / 0 @residual) で genuine closure。** 旧 statement-level pass-through plan (CLOSED) と `mac-l1-discharge-moonshot-plan.md` (partial discharge) を **本 genuine-closure 計画で置換**。旧版の本文は git 履歴。
>
> **親整合 注記 (要 orchestrator アクション、本 planner は roadmap / README 不可侵)**: **Phase A2 (genuine MAC converse、per-letter 条件付き MI 和形) が proof done に達した** (sorryAx-free + 独立 honesty 監査 `@audit:ok`、下記 A2 節)。よって converse はもう scope-out ではない。orchestrator が同期すべき 2 点:
> - (a) **roadmap Ch.15 行 + judgment #10**: 「MAC main = scope-out」→「**converse genuine-closed / achievability pending**」に書換 (converse はもう真壁でも原稿優先でもない、achievability gap2 のみ残)。
> - (b) **README**: 推奨は **full capacity region (converse + achievability) 完成まで defer** — converse 単独行を今足すと「MAC done」と誤読されうる。converse row を先行追加するなら名前は `mac_converse` (genuine per-letter MI 和形) と明記し achievability 未達を併記。判断は orchestrator。

## 進捗

- [x] Phase 0 — MAC 基盤定義 (Basic.lean) ✅ sorryAx-free
- [x] Phase A1 — converse **message-level** (`mac_converse_message_level`、3× 単一ユーザ Fano) ✅ sorryAx-free (genuine MAC converse ではない、A2 が本体)
- [x] Phase A2 — converse **genuine frontier** (single-letterization = 本ゲートウェイ、`mac_converse` per-letter 条件付き MI 和形) ✅ sorryAx-free + `@audit:ok`
- [ ] Phase C-def — 3-way JTS 定義 (JointTypicality.lean、gap1 の定義部のみ) 📋
- [ ] Phase B — achievability gateway atom `macJTS_indep_prob_le_X1` (gap2 E1、analytic 核) 📋 → gateway-atom-first
- [ ] Phase C-rest — JTS 濃度上界 + AEP (gap1 残) 📋
- [ ] Phase D — 4-event Bonferroni + 2-codebook averaging + achievability headline (gap3) 📋
- [ ] Phase V — verify (`lake env lean` + `#print axioms` sorryAx-free + 独立 honesty 監査) 📋

## ゴール / Approach

### Goal (最終定理 signature)

2-user DMC `W : MACChannel α₁ α₂ β = Kernel (α₁ × α₂) β`、有限 alphabet、入力 `p₁ ⊗ p₂` (独立 product)。**corner-point / operational 3 不等式形** を headline にする (full convex hull は L-MAC5 = scope-out)。

```lean
structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop where
  bound₁   : R₁ ≤ I₁            -- I₁ = I(X₁; Y | X₂)
  bound₂   : R₂ ≤ I₂            -- I₂ = I(X₂; Y | X₁)
  boundSum : R₁ + R₂ ≤ Iboth    -- Iboth = I(X₁, X₂; Y)

theorem mac_converse … : InMACCapacityRegion R₁ R₂ I(X₁;Y|X₂) I(X₂;Y|X₁) I(X₁,X₂;Y)

theorem mac_achievability … :
    ∃ N, ∀ n ≥ N, ∃ (M₁ M₂ : ℕ) (_lb₁ _lb₂) (c : MACCode M₁ M₂ n α₁ α₂ β),
      (c.averageErrorProb W).toReal < ε'
```

(inventory §「主定理の最終形」を SoT とする。)

### Approach (overall strategy / shape of solution)

MAC = **単一ユーザ通信路符号化定理の 2-user 一般化**。in-project 機構 (`ChannelCoding/`, `CondMutualInfo`, `Fano/Measure`, `AEP/`) を最大流用し、新規 analytic 核は **1 箇所 (gap2)** に局所化する。攻略は **二段構え**:

1. **converse は 2 段、両段 closure 済 (genuine)**。
   - **A1 = message-level (完成)**: 単一ユーザ Fano 逆定理 `shannon_converse_single_shot` を 3 回適用するだけ (`mac_converse_message_level`、sorryAx-free)。これは genuine MAC converse ではない (`Ys` が符号に未束縛) が、A2 の上流足場。
   - **A2 = genuine frontier (完成、MAC converse の実体)**: 本物の channel-coding converse は **single-letterization** (A2-2) が実体だった。honest genuine 基準 = **単一ユーザ parity** = memoryless/Markov を precondition、generic Fano 誤り項とする per-letter 条件付き MI 和 `Σᵢ I(X₁ᵢ;Yᵢ|X₂ᵢ)` (`mac_converse`、entropy ルート)。当初ゲートウェイと置いた A2-1「操作的 `averageErrorProb` リンク」は **genuineness に不要な別 wrapper** で、単一ユーザにも `averageErrorProb` 結論の操作的 weak converse は存在しない (settled-facts、判断ログ #5)。旧 step-2「壁」は export + det-conditioner Markov 補題の plumbing で解消。

2. **achievability は gap2 = analytic 核を gateway-atom-first で割ってから plumbing**。重い箇所は **3 本の条件付き independent-pair 確率下界** (gap2、E1/E2/E3) ただ 1 つ。残り (gap1 = 3-way JTS + AEP、gap3 = 4-event Bonferroni + 2-codebook averaging) は単一ユーザ機構の同型拡張 = plumbing。よって **gap2 の決定的 1 本 `macJTS_indep_prob_le_X1` (E1 条件付き X₁-fiber 下界) を gateway-atom-first で最初に lean-implementer に dispatch** し、通れば achievability genuine closure 確定 (E2 対称 / E3 は単一ユーザ (c) 流用 / gap1・gap3 は plumbing)、通らなければ gap2 のみ shared sorry 壁に縮退 (撤退ライン参照)。旧 scaffold `IsMACPerEventAEPDecay` が primitive bundle で逃げていた重心 = ここ。

**依存順序 (skeleton)**: `Basic` → `Converse` (独立、A) / `JointTypicality` (C-def) → `AchievabilityCore` (B gateway atom、JTS 定義に依存) → `Achievability` (D headline)。gap2 gateway atom は **JTS 定義 (C-def) が先に要る**ため、C-def を cheap な定義骨格として B より前に置く (card/AEP 等の重い部分 C-rest は B の後で良い)。

**Mathlib-shape-driven (CLAUDE.md 規約)**: corner cut rate `I(X₁;Y|X₂)` 等は **既存 `condMutualInfo` の結論形をそのまま返す**よう定義する (textbook の `H(...)` 差分直書きを避ける)。`MACChannel := Kernel (α₁×α₂) β` は単一ユーザ `Channel` の codomain-pair 版、`MACCode` は encoder×2 + pair-decoder。これにより A1 の chain rule / Fano が型整合で直接適用できる。

### 型クラス設定 (inventory「事故注意ボックス」verbatim)

```lean
variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β]  [DecidableEq β]  [Nonempty β]  [MeasurableSpace β]  [MeasurableSingletonClass β]
```

`condMutualInfo` / `mutualInfo_chain_rule` / `condMutualInfo_chain_rule_X_2var` は X/Y/(Z=X₂) 側に **`[StandardBorelSpace _] [Nonempty _]` を verbatim 要求**。有限 alphabet では `[Countable]+[MeasurableSingletonClass] → [DiscreteMeasurableSpace] → [StandardBorelSpace]` の instance chain で **自動 derive** (Fano Phase 3 で実証済の経路) → corner-point form では明示追加不要。**ただし条件付け側 Z=X₂ の型クラスも揃える**こと (上記 variable で充足)。

---

## Phase 0 — MAC 基盤定義 (greenfield、規模小、リスク低)

**ファイル**: `InformationTheory/Shannon/MultipleAccess/Basic.lean`
**proof-log**: no (定義 + 自明性質のみ、proof done が自明)

- [ ] `abbrev MACChannel α₁ α₂ β := Kernel (α₁ × α₂) β`
- [ ] `structure MACCode (M₁ M₂ n) (α₁ α₂ β)` — `encoder₁ : Fin M₁ → (Fin n → α₁)` / `encoder₂ : Fin M₂ → (Fin n → α₂)` / `decoder : (Fin n → β) → Fin M₁ × Fin M₂`
- [ ] error event + per-pair 誤り確率: `MACCode.errorProbAt c W (m₁,m₂) := Measure.pi (fun i ↦ W (enc₁ m₁ i, enc₂ m₂ i)) (errorEvent …)` (3 誤り事象 = decoder が (m₁,m₂) 以外を返す)、`averageErrorProb` (M₁·M₂ 正規化)
- [ ] 基本性質: `mac_errorProbAt_le_one` / `mac_averageErrorProb_le_one` / `mac_averageErrorProb_ne_top` (単一ユーザ `averageErrorProb_le_one` 同型)
- [ ] **corner cut rate 定義** (Mathlib-shape-driven、`condMutualInfo` 結論形を直接返す): `I₁ = condMutualInfo μ X₁ Y X₂` / `I₂ = condMutualInfo μ X₂ Y X₁` / `Iboth = mutualInfo μ (fun ω ↦ (X₁ ω, X₂ ω)) Y`
- [ ] `structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop` (3 field) + `mk'` / `iff_and` / `mono` 等の基本 lemma

**設計選択 (inventory §D 所見、確定)**: 凸包 / closure は Mathlib 完備 (`convexHull` :46 / `closedConvexHull_eq_closure_convexHull` :332) だが gap でなく**設計選択**。**headline は corner-point form (`InMACCapacityRegion` の 3 不等式)** とし、time-sharing 全凸包 (L-MAC5) は scope-out 維持。full hull form は将来 §B 借用で別途。

- **依存 in-project decl**: `ChannelCoding/Basic.lean:145` (`Code`)、`:192` (`errorProbAt`)、`:207` (`averageErrorProb_le_one`); Mathlib `Measure.pi` (`Pi.lean:212`, `irreducible_def` — `pi_pi` API 経由で評価、直 unfold 不可)
- **gateway atom**: 無し (定義 Phase)。リスク低、greenfield。
- **撤退条件**: 定義が `condMutualInfo` 結論形と噛み合わない場合のみ Mathlib-shape-driven 再定義 (CLAUDE.md 第一選択)。**load-bearing hyp / `Prop := True` slot 禁止** (旧 scaffold の `IsMAC...Passthrough` を踏襲しない)。Phase 0 は genuine、sorry 不要。

---

## Phase A1 — converse message-level ✅ DONE (sorryAx-free) — **genuine MAC converse ではない**

**ファイル**: `InformationTheory/Shannon/MultipleAccess/Converse.lean` (+ `Basic.lean` の `MACChannel`/`MACCode`/`errorProbAt`/`averageErrorProb`/`InMACCapacityRegion`/`InMACCapacityRegion.mono`)
**proof-log**: no (完成済、3× 単一ユーザ converse の機械的適用)

完成内容 (commit `97869bf9` で独立 honesty 監査済、`#print axioms` sorryAx-free):

- `mac_converse_message_level` (= 旧 `mac_converse`、`@[entry_point]`) + `mac_converse_bound₁`/`mac_converse_bound₂`/`mac_converse_bound_sum`。`shannon_converse_single_shot` を、条件付けメッセージを **出力スロット**に置いて 3 回適用し `InMACCapacityRegion` に詰めるだけ。
- 情報量スロット = n-letter の **メッセージ間 MI**: `(mutualInfo μ Msg₁ (Msg₂,Yⁿ)).toReal + binEntropy(Pe₁) + Pe₁·log(M₁−1)` 等。独立メッセージ下で `I(M₁;(M₂,Yⁿ)) = I(M₁;Yⁿ|M₂)` (converse 中間量)。
- `InMACCapacityRegion.mono` (情報量上界を緩めても rate pair が領域内に残る) を **message-level → single-letter への橋**として実装済 (A2 で使う): A2 が `message-level info ≤ Σᵢ per-letter info` を示せば `.mono` で single-letter form に降ろせる。

**重要 (監査所見、commit `97869bf9`)**: A1 は **genuine MAC converse ではない**。`Ys : Fin n → Ω → β` が **任意の可測関数**で、`MACChannel W` にも memoryless 構造にも `MACCode.encoder₁/encoder₂` → channel 出力にも束縛されておらず、Fano の誤り `MeasureFano.errorProb …` も `MACCode.averageErrorProb W`/`errorProbAt` (Basic.lean、操作的ブロック誤り) と結線されていない。論理は true だが「符号についての converse」ではなく headline 名が overclaim だった → `mac_converse` → `mac_converse_message_level` に rename 済 (genuine な `mac_converse` は A2 が取得)。

---

## Phase A2 — converse genuine frontier (single-letterization) ✅ DONE (genuine, sorryAx-free, `@audit:ok`)

**ファイル**: `InformationTheory/Shannon/MultipleAccess/Converse.lean` (A1 と同一ファイル)
**proof-log**: yes (commit `3a8dbc6d` / `383a0807` / `56563e17`、再開根拠保存済)

**closure 結果**: per-letter 条件付き MI 和形 `mac_converse` を genuine 完成。全 decl `#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free)、独立 honesty 監査 `@audit:ok`、Converse.lean 内 0 sorry / 0 @residual。再検算 → settled-facts 節。

**ゲートウェイ反転 (本 reconcile の核、判断ログ #5 に集約)**: 当初の計画はゲートウェイを **A2-1 (操作的 `averageErrorProb` リンク)** と置き A2-2 を後回しにしていたが、**これは誤り — 実際のゲートウェイは A2-2 (single-letterization)** だった。verbatim 所見が反転を駆動した: 単一ユーザ `ChannelCoding/` ツリーに `c.averageErrorProb W` を結論に持つ weak (Fano) 操作的逆定理は **存在しない**。genuine な単一ユーザ終端 (`channel_coding_converse_general_memoryless_pure` 等) は全て generic な `MeasureFano.errorProb` を使い、`IsMemorylessChannel` + block-Markov を **構造的 precondition** とする。よって **honest な genuine 基準 = 単一ユーザ parity** = per-letter 条件付き MI 和 `Σᵢ I(X₁ᵢ;Yᵢ|X₂ᵢ)` を memoryless/Markov を precondition、generic Fano 誤り項で出す形。**A2-1 の操作的リンク (uniform message → encoder → memoryless W joint を組み誤りを `MACCode.averageErrorProb W` と同定) は genuineness に不要** = 別個の任意 wrapper (本計画スコープ外)。→ 将来の leg が A2 を「操作的 μ 構成が必要」と再 scope しないこと。

**closure した decl (全 `Converse.lean`、sorryAx-free)**:

- `condMutualInfo_singleletter_le_of_memoryless` — genuine な analytic 核 (step 3 = 条件付き single-letterization `I(X₁ⁿ;Yⁿ|X₂ⁿ) ≤ Σᵢ I(X₁ᵢ;Yᵢ|X₂ᵢ)`、entropy ルート)。
- `condEntropy_pi_le_sum_condEntropy` — 再利用可能な条件付き subadditivity 副産物。
- `mac_message_le_condMI` — step 1+2 (step-2 DPI `I(M₁;Yⁿ|M₂) ≤ I(X₁ⁿ;Yⁿ|X₂ⁿ)` を entropy ルート OL-1/OL-2 で closure)。
- `mac_singleletterize_bound₁`/`₂`/`sum` — 3 本の single-letterization bound (bound₂ は swap した `MACCode` 経由、bound_sum は無条件で単一ユーザ `mutualInfo_le_sum_per_letter_of_memoryless_strong` を流用)。
- `mac_converse` (`@[entry_point]`、`@audit:ok`) — 3 bound を `InMACCapacityRegion.mono` 経由で `InMACCapacityRegion` に詰める genuine per-letter 和形 headline。
- `mac_converse_message_level` (A1) は intact 保持。
- infra: `isMarkovChain_swap` + `isMarkovChain_map_conditioner_measurableEquiv` を private→public export、新規 public `isMarkovChain_comp_conditioner_right` (条件子の決定的関数の Markov 性) を `CondEntropyMemoryless.lean` に追加。

**旧「step-2 壁」は plumbing で壁ではなかった** — export + det-conditioner Markov 補題で closure 済 (cause:plumbing)。Converse.lean に residual なし。

**honest target (L-MAC5 と区別、維持)**: 達成 converse は **per-letter 和形** (各時刻の周辺入力分布での和)。固定 product input `p(x₁)p(x₂)` での single-letter 領域は time-sharing/凸包 (L-MAC5 = scope-out) を要し本計画対象外。

---

## Phase C-def — 3-way JTS 定義 (gap1 定義部、Phase B の前提)

**ファイル**: `InformationTheory/Shannon/MultipleAccess/JointTypicality.lean`
**proof-log**: no (定義 + 可測性、軽量)

- [ ] `macJointSequence X1s X2s Ys i ω := (X1s i ω, X2s i ω, Ys i ω)` + `measurable_macJointSequence`
- [ ] `macJointlyTypicalSet μ X1s X2s Ys n ε : Set ((Fin n→α₁)×(Fin n→α₂)×(Fin n→β))` = **4 単軸 typicalSet の交差** (X₁-, X₂-, Y-, joint-axis、α₁×α₂×β 上 iterated-pairing)
- [ ] `mem_macJointlyTypicalSet_iff` / `measurableSet_…` / `…_finite`

- **依存 in-project decl**: `ChannelCoding/Basic.lean:281` (2-user `jointlyTypicalSet`、3-axis 化のひな型); `AEP/` の単軸 `typicalSet` 群; Mathlib `MeasurableEquiv.arrowProdEquivProdArrow` / `prodAssoc` (3-tuple reshape)
- **gateway atom**: 無し (定義 Phase)。**B の前提**ゆえ B より前に骨格を置く。
- **撤退条件**: 定義 Phase、sorry 不要。旧 `MACL1Discharge.lean` が同手法で sorry-free 達成歴あり = リスク極低。

---

## Phase B — achievability gateway atom `macJTS_indep_prob_le_X1` (gap2 E1、analytic 核) 🎯 gateway-atom-first

**ファイル**: `InformationTheory/Shannon/MultipleAccess/AchievabilityCore.lean`
**proof-log**: yes (条件付き fiber 解析は本計画唯一の重い analytic 核、再開根拠に必須)

- [ ] **gateway atom `macJTS_indep_prob_le_X1`** (E1、X₁ だけ別 codeword): `(X̃₁, X₂, Y)` で X̃₁ ⟂ (X₂,Y) のとき JTS に入る確率 ≤ `exp(-n(I(X₁;Y|X₂) - 3ε))`。単一ユーザ `jointlyTypicalSet_indep_prob_le` (`Basic.lean:540`、`exp(-n(I-3ε))`) の **条件付き X₁-fiber 版** (X₂ を固定して X₁-fiber 上の typical 質量を測る Slepian-Wolf 風 slice、entropy 分解で指数が `I(X₁;Y|X₂)` になる)。
  - **まず lean-implementer に本 atom 1 本を dispatch** (gateway-atom-first)。通るか否かが achievability genuine-closure 可否の決定打。
- [ ] **E2** `macJTS_indep_prob_le_X2` (X₂ だけ別): E1 の対称 (≤ `exp(-n(I(X₂;Y|X₁) - 3ε))`)
- [ ] **E3** `macJTS_indep_prob_le_both` (両方別、(X̃₁,X̃₂) ⟂ Y): 単一ユーザ (c) の **直接 3-axis 類比** (≤ `exp(-n(I(X₁,X₂;Y) - 3ε))`、軽い)

- **依存 in-project decl**: `ChannelCoding/Basic.lean:540` (`jointlyTypicalSet_indep_prob_le`、E1/E2/E3 のひな型); `:320` (`jointlyTypicalSet_card_le`); C-def の `macJointlyTypicalSet`; `MutualInfo.lean:122` (`mutualInfoOfChannel_eq_HX_add_HY_sub_HZ`、指数 = `H(Z₀)-H(X₀)-H(Y₀) = -I` の条件付き類比); 前提 `iIndepFun (fun i ↦ Xs i) μ` (full mutual independence、pairwise 不足) + per-letter iid
- **gateway atom**: `macJTS_indep_prob_le_X1` (E1)。通れば E2 対称 / E3 流用で連鎖 = achievability genuine closure 確定。
- **予想規模**: ~400-600 行 (E1/E2 条件付き fiber が新規、E3 は (c) 流用で軽い)。**本計画の重心 (唯一の重い analytic gap)**。
- **撤退条件**: gateway atom dispatch が **通らない**場合のみ E1/E2/E3 を **3 本の shared sorry 補題** `@residual(wall:joint-typicality-multi)` で開ける (register 済壁、audit-tags.md「Shared Mathlib walls」)。achievability headline (Phase D) は **これら sorry 補題を直接呼び出す**形で受ける (`*Hypothesis` predicate に bundle しない = 旧 `IsMACPerEventAEPDecay` primitive bundle 禁止)。converse (Phase A) は壁なしゆえ achievability 縮退時も単独で proof done 到達可能。

---

## Phase C-rest — JTS 濃度上界 + AEP (gap1 残、規模中、リスク低)

**ファイル**: `JointTypicality.lean` (C-def と同一ファイル)
**proof-log**: no (旧 scaffold で sorry-free 実証済の手法)

- [ ] `macJointlyTypicalSet_card_le` — φ-injection で 4-tuple JTS を α₁×α₂×β 上単軸 typicalSet に埋込 → `typicalSet_card_le`。結論 `card ≤ exp(n·(H(X₁,X₂,Y)+ε))`
- [ ] `macJointlyTypicalSet_prob_tendsto_one` (E0、正解 pair が typical) — 4 単軸 good event の交差、`measure_inter3_tendsto_one` (`Basic.lean:378` private) の 4-event 版へ拡張、各 `typicalSet_prob_tendsto_one`
- [ ] (任意) rate ベース下界 `macJointlyTypicalSet_prob_ge_of_rate` — E0 を `1-η` で押さえる closed-form N (`AEP/Rate.lean:391` を 3-axis 化)

- **依存 in-project decl**: `ChannelCoding/Basic.lean:320` (`jointlyTypicalSet_card_le`)、`:450` (`jointlyTypicalSet_prob_tendsto_one`)、`:378` (`measure_inter3_tendsto_one` private); `AEP/Rate.lean:391`
- **gateway atom**: `macJointlyTypicalSet_card_le` (φ-injection)。**低リスク** (旧 `MACL1Discharge.lean` で sorry-free 達成歴)。
- **予想規模**: ~200-300 行。
- **撤退条件**: 詰まった補題のみ `sorry` + `@residual(plan:mac-joint-typicality-plan)`。発動見込み低 (構築可)。

---

## Phase D — 4-event Bonferroni + 2-codebook averaging + achievability headline (gap3、plumbing)

**ファイル**: `InformationTheory/Shannon/MultipleAccess/Achievability.lean`
**proof-log**: yes (2-codebook averaging + random→deterministic の凸結合論法は手数が多い)

- [ ] **D-1 4-event Bonferroni**: per-codeword pair 誤り ≤ E0 + E1 + E2 + E3 の union bound。gateway atom `mac_errorProbAt_le_bonferroni4` (4-event subset、`Achievability/Core.lean:83` の `errorProbAt_le_E1_plus_E2` を 4-event 拡張、union-bound は同型 plumbing)
- [ ] **D-2 2-codebook 期待値**: `Codebook M₁ n α₁ × Codebook M₂ n α₂` の独立積上で期待値 ≤ ∑ 各 event 期待値 (Fubini / IndepFun は `iIndepFun_infinitePi` 既存パターン、`iidAmbientMeasure`)
- [ ] **D-3 random → deterministic**: `exists_codebook_le_avg` (`Achievability/Main.lean:47`) の凸結合論法を 2-codebook 版に拡張 (`random_codebook_average_le` `RandomCodebook.lean:1157` 同型)
- [ ] **D-4 headline `mac_achievability`**: `R₁<I₁ ∧ R₂<I₂ ∧ R₁+R₂<Iboth` で全 4 項 →0 → `∃ codebook, avgErr < ε'`。template = 単一ユーザ `channel_coding_achievability` (`Achievability/Main.lean:219`、1 rate→rate pair / 1 codebook→2 codebook / E1+E2→E0..E3)

- **依存 in-project decl**: `Achievability/Core.lean:50/56/68/83/216` (`Codebook`/`jointTypicalDecoder`/`codebookToCode`/`errorProbAt_le_E1_plus_E2`/`codebookMeasure`); `Achievability/Main.lean:47/219`; `RandomCodebook.lean:1157`; Phase B の E0..E3 bound
- **gateway atom**: `mac_errorProbAt_le_bonferroni4` (4-event subset)。**低リスク** (union bound plumbing)。
- **予想規模**: ~400-500 行 (大半が機械的拡張、旧 `MACRandomCodebookAveraging.lean` がひな型)。
- **撤退条件**: 詰まった補題のみ `sorry` + `@residual(plan:mac-achievability-bonferroni-plan)`。旧 scaffold `IsMACExpectationDecomp` / `IsMACRandomCodebookMarkov` の予測 bundle は **踏襲禁止** (averaging 凸結合のみ genuine、4-event 期待値分解は自作で開ける)。

---

## Phase V — verify

**proof-log**: no

- [ ] 各ファイル `lake env lean …` silent (sorry warning のみ許容、type-check done)
- [x] proof done 判定: `mac_converse_message_level` (A1) / `mac_converse` (A2 genuine) が `#print axioms` で sorryAx 非依存 (`[propext, Classical.choice, Quot.sound]`) を機械確認済。残: `mac_achievability` (Phase D)
- [ ] 新規 `sorry` + `@residual` 導入 commit があれば **独立 honesty 監査** (`honesty-auditor`) を session 内で起動 (orchestrator-mandatory)
- [ ] `InformationTheory.lean` に 5 ファイル import 追加 (Basic → JointTypicality → AchievabilityCore → Achievability、Converse は Basic のみ依存)

---

## ファイル配置 (単一ユーザ `ChannelCoding/` 構成を踏襲)

```
InformationTheory/Shannon/MultipleAccess/
  Basic.lean              -- Phase 0: MACChannel / MACCode / errorProb / InMACCapacityRegion / corner cut rate
  Converse.lean           -- Phase A: gap4 (Fano + chain rule + DPI、Basic のみ依存、独立)
  JointTypicality.lean    -- Phase C: gap1 (3-way JTS 定義 + 濃度上界 + AEP)
  AchievabilityCore.lean  -- Phase B: gap2 (E1/E2/E3 条件付き independent-pair 下界、gateway atom)
  Achievability.lean      -- Phase D: gap3 (4-event Bonferroni + 2-codebook averaging + headline)
```

import 連鎖: `Basic` ← {`Converse`, `JointTypicality`}; `JointTypicality` ← `AchievabilityCore` ← `Achievability`。各実装 agent は `InformationTheory.lean` を編集せず、orchestrator が最後に import 5 本をまとめて追加。

---

## 撤退ライン / honesty

撤退口は **`sorry` + `@residual(<class>:<slug>)` のみ** (CLAUDE.md「検証の誠実性」)。load-bearing `*Hypothesis` / `*Reduction` / `IsXxxClaim` predicate に証明の核を bundle するのは禁止 — 旧 scaffold の `IsMACPerEventAEPDecay` (primitive "Mathlib gap passed through") / `IsMAC...Passthrough` / `Prop := True` slot は **pass-through であって proof done ではない**ので踏襲しない。regularity hyp (full-support `h_pos` / `IsProbabilityMeasure` / 可測性 / `iIndepFun` / uniform message) は **precondition で OK**。

frozen slug (他 doc / 旧 plan が参照、削除不可):

- **L-MAC1** (multi-user joint typicality body): gap1 (Phase C) が触れる。**achievability 残・open**。gateway `macJointlyTypicalSet_card_le` で genuine 化、旧 scaffold sorry-free 達成歴あり → 発動見込み低。
- **L-MAC2** (multi-user Fano + chain rule): **RESOLVED** (genuine MAC converse 完成、Phase A2)。message-level (A1) + genuine single-letterization (A2 = `mac_converse`、entropy ルート、cause:plumbing で旧 step-2「壁」を解消) の双方を sorryAx-free + `@audit:ok` で closure。
- **L-MAC3** (inner bound existence pass-through): gap2+gap3 (Phase B/D) が触れる。**achievability 残・open**。gap2 が唯一の重い analytic 核 → gateway-atom-first で genuine 化試行。
- **L-MAC4** (outer bound `InMACCapacityRegion` pass-through): **RESOLVED** (genuine outer bound = per-letter 和形 `mac_converse` 完成、Phase A2)。`InMACCapacityRegion` predicate は load-bearing でない generic bundle。
- **L-MAC5** (time-sharing 全凸包): **scope-out 維持** (撤退ライン明記)。corner-point form のみが genuine target。full hull は §B `convexHull` で将来対応 (本タスク対象外)。

**唯一の register 済壁** (achievability 側、converse は壁なしで closure 済): gap2 不通時の退避先 = `@residual(wall:joint-typicality-multi)` (audit-tags.md、Ch.15 MAC/BC/Relay)。**ただし gateway-atom-first で E1 を試し、通れば壁ではなく genuine closure** (CLAUDE.md「壁判定は反証を 1 度試みる」)。

---

## settled-facts (minimal、再導出可能なものは都度 `rg` / `#print axioms`)

- Phase 0 + A1 + **A2 (genuine converse) 実装済** (commits `97869bf9` / `3a8dbc6d` / `383a0807` / `56563e17`): `Basic.lean` + `Converse.lean` (`mac_converse` per-letter 和形 genuine headline + `mac_message_le_condMI` + `condMutualInfo_singleletter_le_of_memoryless` + `mac_singleletterize_bound₁/₂/sum` + A1 の `mac_converse_message_level`)、全 sorryAx-free + `@audit:ok`。再検算: `lake env lean InformationTheory/Shannon/MultipleAccess/Converse.lean` silent + `#print axioms mac_converse` = `[propext, Classical.choice, Quot.sound]`。残りの achievability (`macJointlyTypicalSet` 等) は未実装 = greenfield (`rg` で確認、再導出可)。
- **単一ユーザに操作的 weak converse は不在** (genuine 基準を決めた所見、confidence loogle-neg/grep): 単一ユーザ `ChannelCoding/` ツリーで `c.averageErrorProb W` を結論に持つ Fano 逆定理は **0 件** — genuine 終端は全て generic `MeasureFano.errorProb` + `IsMemorylessChannel`/block-Markov を precondition とする。よって MAC の honest genuine 基準も per-letter 条件付き MI 和 + generic 誤り項 (操作的 `averageErrorProb` joint は genuineness に不要な別 wrapper)。
- Mathlib に typical-set / jointly-typical 概念は **完全不在** (loogle `typicalSet` / `jointlyTypical` = unknown identifier、confidence loogle-neg)。typical-set machinery は in-project `AEP/` が唯一の出所。

(これ以上のキャッシュはしない。`docs/shannon/mac-facts.md` は現時点で作らない。)

---

## 判断ログ

append-only。決着済 entry は削除 (git が履歴)、active のみ残す。≤ 10 entry。

1. **region 表現 = corner-point form 確定**: `InMACCapacityRegion` の 3 不等式を headline とする。凸包 / closure は Mathlib 完備 (`convexHull` / `closedConvexHull_eq_closure_convexHull`) で **gap でなく設計選択**、time-sharing 全凸包 (L-MAC5) は scope-out 維持。full hull form は将来別途。
2. **achievability 攻略順序 (active、converse は closure 済)**: gap2 E1 gateway atom `macJTS_indep_prob_le_X1` を **gateway-atom-first で dispatch** → 通れば E2 対称 / E3 流用 + gap1/gap3 plumbing で genuine closure 確定、不通なら gap2 のみ shared sorry 壁に縮退 (#3)。
3. **gap2 撤退の honest 形**: gateway atom 不通時のみ E1/E2/E3 を **3 本の shared sorry 補題** `@residual(wall:joint-typicality-multi)` で開け、headline はそれを **直呼び** (predicate bundle 禁止、旧 `IsMACPerEventAEPDecay` を踏襲しない)。
4. **親整合 (要 orchestrator アクション、active)**: converse が genuine-closed になったので、orchestrator が roadmap Ch.15 行 + judgment #10 を「scope-out」→「converse genuine-closed / achievability pending」に書換 + README 方針決定 (推奨 = full region 完成まで defer)。本 planner は roadmap / README 不可侵 (editing boundary 外)。詳細 → 冒頭「親整合 注記」。
5. **A2 closed + ゲートウェイ反転の教訓 (#5〜#8 を集約、settled)**: L-MAC2/L-MAC4 を genuine MAC converse `mac_converse` (per-letter 条件付き MI 和形) で closure (commits `3a8dbc6d`/`383a0807`/`56563e17`、sorryAx-free + `@audit:ok`)。**教訓 = ゲートウェイ反転**: 当初 A2-1 (操作的 `averageErrorProb` リンク) をゲートウェイと置いたが誤りで、実体は A2-2 (single-letterization)。単一ユーザに `averageErrorProb` 結論の操作的 weak converse が不在 (settled-facts) ゆえ honest genuine 基準 = generic Fano + memoryless precondition の per-letter MI 和 = 単一ユーザ parity。inventory の「converse 純配線」は A1/A2 混同だった (cause:plumbing で旧 step-2「壁」も解消)。rename (`mac_converse`→`mac_converse_message_level`) + docstring ref 是正は実施済 (git 履歴)。

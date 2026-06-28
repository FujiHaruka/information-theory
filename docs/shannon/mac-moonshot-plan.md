# MAC (Multiple Access Channel) Capacity Region — genuine-closure ムーンショット計画 🌙

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §Ch.15 (Network IT / DSC mini-chapter)
> **Inventory**: [`mac-inventory.md`](mac-inventory.md) (§A in-project 流用 / §B Mathlib / §C 削除済 scaffold 型 / §D gap)

> **Status**: Drafting (greenfield)。**目標 = Cover–Thomas 2nd ed. Theorem 15.3.1 (2-user DMC capacity region) を標準B (proof done = 0 sorry / 0 @residual) で genuine closure。** 旧 statement-level pass-through plan (CLOSED) と `mac-l1-discharge-moonshot-plan.md` (partial discharge) を **本 genuine-closure 計画で置換**。旧版の本文は git 履歴。
>
> **親整合 注記**: roadmap Ch.15 行は現在 **MAC main = scope-out** (judgment #10 = 原稿優先、真壁ではない)。本計画はそれを **再開**する。**Phase A1 (converse message-level) は完成済だが genuine MAC converse ではない** — roadmap Ch.15 を「converse 完成」と書いてはいけない (A2 が残る、判断ログ #6/#7)。converse を roadmap で done 扱いにできるのは **Phase A2 (genuine frontier) が proof done に達した時点のみ**。orchestrator が roadmap Ch.15 行 + judgment #10 を同期する (本 planner は roadmap を編集しない、editing boundary 外)。

## 進捗

- [ ] Phase 0 — MAC 基盤定義 (Basic.lean) 📋
- [x] Phase A1 — converse **message-level** (`mac_converse_message_level`、3× 単一ユーザ Fano) ✅ sorryAx-free — **ただし genuine MAC converse ではない** (下記)
- [ ] Phase A2 — converse **genuine frontier** (操作的誤り→情報量リンク + single-letterize、これが MAC converse の実体) 📋
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

1. **converse は 2 段** (当初「gap4 = 壁なし純配線で 1 段完成」と見積もったが過小評価、判断ログ #6)。
   - **A1 = message-level (完成済)**: 単一ユーザ Fano 逆定理 `shannon_converse_single_shot` を、条件付けメッセージを **出力スロット**に置いて 3 回適用するだけ (`mac_converse_message_level` = 旧 `mac_converse`、sorryAx-free)。情報量スロットは n-letter の **メッセージ間 MI** `I(M₁;(M₂,Yⁿ)).toReal + Fano 項` 等。**これは genuine MAC converse ではない**: `Ys` は任意の可測関数で `MACChannel W` にも memoryless 構造にも `MACCode` の操作的ブロック誤り (`averageErrorProb`/`errorProbAt`) にも束縛されていない (= 「符号についての converse」になっていない)。論理は true だが headline 名が overclaim。
   - **A2 = genuine frontier (未達、MAC converse の実体)**: A1 の message-level 結論を **操作的誤りリンク** + **single-letterize** で本物の channel-coding converse に降ろす。inventory が「壁なし純配線」と判定したのは A1 のことで、A2 (channel W・memoryless・操作的誤りへの結線) こそ実体。Mathlib 道具 (`condMutualInfo_chain_rule_X_2var` / `condMutualInfo_le_of_markov_joint` / `condDistrib`) は揃っているが「純配線」ではなく **converse の核心** = gateway-atom-first で genuine 可否を判定する。

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

**重要 (監査所見、commit `97869bf9`)**: A1 は **genuine MAC converse ではない**。`Ys : Fin n → Ω → β` が **任意の可測関数**で、`MACChannel W` にも memoryless 構造にも `MACCode.encoder₁/encoder₂` → channel 出力にも束縛されておらず、Fano の誤り `MeasureFano.errorProb …` も `MACCode.averageErrorProb W`/`errorProbAt` (Basic.lean、操作的ブロック誤り) と結線されていない。論理は true だが「符号についての converse」ではなく、headline 名が overclaim。**orchestrator が `mac_converse` → `mac_converse_message_level` に rename** (本 planner はコードを編集しない)。

---

## Phase A2 — converse genuine frontier (操作的誤り→情報量リンク + single-letterize) 🎯 MAC converse の実体・未達

**ファイル**: `InformationTheory/Shannon/MultipleAccess/Converse.lean` (A1 と同一、A2 用の補題群 + headline `mac_converse` を追加)
**proof-log**: yes (操作的 joint 構成 + per-letter 相殺 + finiteness 供給は手数が多く、再開根拠に必須)

**honest target (重要、L-MAC5 と区別)**: 達成する converse は **per-letter 和形** — `(1/n)·log Mₖ ≤ (1/n)·Σᵢ I(X₁ᵢ;Yᵢ|X₂ᵢ)` 等 (各時刻の周辺入力分布での和)。**固定 product input `p(x₁)p(x₂)` での single-letter 領域は time-sharing/凸包を要し L-MAC5 = scope-out**。A2 target は per-letter 和 (固定 p 領域ではない)。textbook の単一分布形への還元は凸性 (time-sharing) ステップで、本タスク対象外。

2 つの missing piece (これが MAC converse の実体):

- [ ] **A2-1 操作的誤り → 情報量上界リンク** (inventory が見落とした実体): converse の ambient `μ` を、**uniform message pair → encoder₁/encoder₂ → memoryless channel `W`** で構成し、`Ys` をその channel 出力に束縛する。`X₁ᵢ ω := c.encoder₁ (Msg₁ ω) i`、`X₂ᵢ ω := c.encoder₂ (Msg₂ ω) i`、`Yⁿ ~ Measure.pi (fun i ↦ W (X₁ᵢ, X₂ᵢ))`。この `μ` 上で **A1 の message-level errorProb = `c.averageErrorProb W`** (または `≤`) を同定する。単一ユーザ `channel_coding_converse_general_memoryless_pure` (`ConverseMemoryless.lean:627`) が単一ユーザでまさにこの joint を組んでいる = **2-user 版テンプレ**。**現状 `Ys` が符号に未束縛**ゆえ A1 は vacuous に近い (任意の `Ys` で成立) = ここが converse の核心。
- [ ] **A2-2 single-letterize** (channel W・memoryless 構造への結線): `I(Mₖ;Yⁿ|M_other) ≤ Σᵢ I(X₁ᵢ;Yᵢ|X₂ᵢ)` を A2-1 で組んだ memoryless joint 上で示す。
  - **A2-2a 独立還元**: `I(M₁;(M₂,Yⁿ)) → I(M₁;Yⁿ|M₂)` (chain rule `mutualInfo_chain_rule` `CondMutualInfo.lean:214` + メッセージ独立 `I(M₁;M₂)=0`)。
  - **A2-2b chain rule**: `condMutualInfo_chain_rule_X_2var` (`ConverseMemorylessChainRule.lean:164`) で n-letter → ∑ per-letter。
  - **A2-2c per-letter DPI**: `condMutualInfo_le_of_markov_joint` (`ConverseMemorylessChainRule.lean:113`) で per-letter を memoryless 構造で抑える。2-user `IsMemorylessChannel` (`ConverseMemoryless.lean:66`) を A2-1 の joint で構築。
  - **finiteness 供給** (項相殺の前提、最危険所見): `condMutualInfo_chain_rule_X_2var` の `hWcY_fin` / `condMutualInfo_le_of_markov_joint` の `hWcYo_fin` を有限 alphabet で `mutualInfo_ne_top` (`MutualInfo.lean:174`) / `condMutualInfo_ne_top` (`CondMutualInfo.lean:320`) から供給。**落とすと per-letter 相殺が止まり single-letterize が破綻**。
- [ ] **A2-3 headline `mac_converse`** (genuine): A2-1 + A2-2 を組み、A1 の `mac_converse_message_level` 結論に `InMACCapacityRegion.mono` を適用して per-letter 和形 `InMACCapacityRegion (log M₁) (log M₂) (Σᵢ I(X₁ᵢ;Yᵢ|X₂ᵢ)) … ` に降ろす。`n⁻¹` 正規化で rate 形。

- **依存 in-project decl**: `Basic.lean` (`MACChannel`/`MACCode.encoder₁₂`/`errorProbAt`/`averageErrorProb`); `ConverseMemoryless.lean:66/502/554/627` (memoryless 構造 + 単一ユーザ操作的 joint テンプレ); `ConverseMemorylessChainRule.lean:113/164/243`; `CondMutualInfo.lean:214/285/320`; `MutualInfo.lean:174`; Mathlib `condDistrib` / `Measure.pi` (操作的 joint 構成)
- **gateway atom** (gateway-atom-first、決定打): **`mac_converse_operational_link`** = A2-1 = 「uniform-message → encoder → memoryless W joint を構成し、A1 の message-level errorProb が `c.averageErrorProb W` と同定 (≤) できる + その joint が memoryless/Markov 構造を満たす」を 1 本で示す補題。これが通れば A2-2 (single-letterize) は in-project chain-rule/DPI 道具で連鎖でき genuine closure 公算高。**最初にこれを lean-implementer に dispatch** — A1 が vacuous に近い真因 (符号未束縛) がここで解消するか否かが converse genuine 化の可否を決める。A2-2 単独 (`mac_singleletterize_bound₁`) を gateway にしない理由: A2-1 で memoryless joint が組めて初めて A2-2 の Markov/finiteness 前提が成立する (両者は coupled、上流は A2-1)。
- **予想規模**: ~400-700 行 (A2-1 操作的 joint 構成が新規の重心 = 単一ユーザテンプレの 2-user 化、A2-2 は道具流用だが finiteness threading で手数)。**inventory の「converse ~95% 既存・純配線」は A1 (easy) の見積で、A2 が実体** (判断ログ #6)。
- **撤退条件**: A2 で詰まった step のみ `sorry` + `@residual(plan:mac-moonshot-plan)` (本親計画の A2 節を closure 先とする、**別 child plan は作らない** — 判断ログ #8)。Converse.lean module docstring (L23) の dangling ref `mac-converse-singleletterize-plan` は **本計画 A2 節で受ける**ので、orchestrator が docstring ref を `mac-moonshot-plan.md` に向け直す (本 planner はコード不可侵)。**A2 を wall と前置きしない** — gateway atom A2-1 を試し、通れば壁ではなく genuine closure (CLAUDE.md「壁判定は反証を 1 度試みる」)。load-bearing `MACFanoBound`/`MACSingleFanoBound`/`IsMAC...Passthrough` predicate bundle (旧 scaffold tier-4/5 defect) は **踏襲禁止**、`Ys` を符号に束縛するのは regularity precondition でなく **A2 の核**なので hyp に逃がさず構成する。

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
- [ ] proof done 判定: headline `mac_converse_message_level` (A1、済) / `mac_converse` (A2 genuine、未) / `mac_achievability` に `#print axioms` で sorryAx 非依存 (`[propext, Classical.choice, Quot.sound]`) を機械確認
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

- **L-MAC1** (multi-user joint typicality body): gap1 (Phase C) が触れる。gateway `macJointlyTypicalSet_card_le` で genuine 化、旧 scaffold sorry-free 達成歴あり → **発動見込み低**。
- **L-MAC2** (multi-user Fano + chain rule): Phase A が触れる。**部分 overturn**: message-level (A1) は `shannon_converse_single_shot` 3× で genuine 完成済。だが genuine MAC converse (A2 = 操作的誤りリンク + single-letterize) は **「純配線」ではなく converse の実体**で未達。道具 (`condMutualInfo_chain_rule_X_2var` 等) は完備だが、A2-1 操作的 joint 構成が新規重心 → gateway-atom-first で genuine 可否判定。
- **L-MAC3** (inner bound existence pass-through): gap2+gap3 (Phase B/D) が触れる。gap2 が唯一の重い analytic 核。**overturn 候補** (gateway-atom-first で genuine 化試行)。
- **L-MAC4** (outer bound `InMACCapacityRegion` pass-through): A1 で message-level form が genuine 化済 (`InMACCapacityRegion` predicate は load-bearing でない generic bundle)。genuine outer bound (per-letter 和形) は A2 完了で確定。
- **L-MAC5** (time-sharing 全凸包): **scope-out 維持** (撤退ライン明記)。corner-point form のみが genuine target。full hull は §B `convexHull` で将来対応 (本タスク対象外)。

**唯一の register 済壁**: gap2 不通時の退避先 = `@residual(wall:joint-typicality-multi)` (audit-tags.md:77、Ch.15 MAC/BC/Relay)。**ただし gateway-atom-first で E1 を試し、通れば壁ではなく genuine closure** (CLAUDE.md「壁判定は反証を 1 度試みる」)。converse 側 A2 は register 済壁ではない (道具完備) が **「壁なし = 自明完成」ではない** — A2-1 操作的 joint 構成が実体ゆえ撤退口は `@residual(plan:mac-moonshot-plan)` (本親計画 A2 節)。

---

## settled-facts (minimal、再導出可能なものは都度 `rg` / `#print axioms`)

- Phase 0 + A1 は **実装済** (commit `97869bf9`): `Basic.lean` (`MACChannel`/`MACCode`/`errorProbAt`/`averageErrorProb`/`InMACCapacityRegion`/`.mono`) + `Converse.lean` (`mac_converse_message_level` = 旧 `mac_converse` + `bound₁/₂/sum`)、sorryAx-free。残りの `macJointlyTypicalSet` 等は未実装 = greenfield (`rg` で確認、再導出可)。
- **rename ripple (orchestrator 用、機械確認済)**: `mac_converse` → `mac_converse_message_level` の term-level consumer は **0 件** (`@[entry_point]` 終端 headline、他 decl から参照なし)。text 参照は `Converse.lean` module/decl docstring + `Basic.lean:134` docstring + 本計画 + inventory のみ。`docs/readme-theorems.txt` に MAC 行 **なし** → README 表の再生成不要。blast radius 小。
- Mathlib に typical-set / jointly-typical 概念は **完全不在** (loogle `typicalSet` / `jointlyTypical` = unknown identifier、confidence loogle-neg)。typical-set machinery は in-project `AEP/` が唯一の出所。

(これ以上のキャッシュはしない。`docs/shannon/mac-facts.md` は現時点で作らない。)

---

## 判断ログ

append-only。決着済 entry は削除 (git が履歴)、active のみ残す。≤ 10 entry。

1. **region 表現 = corner-point form 確定**: `InMACCapacityRegion` の 3 不等式を headline とする。凸包 / closure は Mathlib 完備 (`convexHull` / `closedConvexHull_eq_closure_convexHull`) で **gap でなく設計選択**、time-sharing 全凸包 (L-MAC5) は scope-out 維持。full hull form は将来別途。
2. **攻略順序 (改訂)**: converse の **message-level (A1) は完成済** (sorryAx-free)。残る converse 重心は **A2 = genuine frontier** (操作的誤りリンク + single-letterize)、gateway atom A2-1 `mac_converse_operational_link` を **gateway-atom-first で dispatch**。achievability は gap2 E1 gateway atom `macJTS_indep_prob_le_X1` を別途 dispatch。
3. **gap2 撤退の honest 形**: gateway atom 不通時のみ E1/E2/E3 を **3 本の shared sorry 補題** `@residual(wall:joint-typicality-multi)` で開け、headline はそれを **直呼び** (predicate bundle 禁止、旧 `IsMACPerEventAEPDecay` を踏襲しない)。
4. **親整合 (要 orchestrator アクション)**: roadmap Ch.15 行は MAC main = scope-out (judgment #10 = 原稿優先、真壁ではない)。本計画はそれを再開する。本 planner は roadmap を編集しない (editing boundary 外)。
5. **L-MAC2 部分 overturn**: message-level converse (A1) は `shannon_converse_single_shot` 3× で genuine 完成 → message-level 部分は overturn 済。だが genuine MAC converse (A2) は道具完備でも「純配線」ではなく **converse の実体** (A2-1 操作的 joint 構成が新規重心) → A2 は overturn 未確定、gateway-atom-first で判定。
6. **inventory converse 規模過小評価 (今回の reconcile 核)**: `mac-inventory.md` の「converse ~95% 既存・gap4 壁なし純配線」は **easy な message-level (A1) と hard な single-letterization+操作的誤りリンク (A2) を混同**していた。A1 は確かに純配線だが genuine MAC converse ではなく (符号 W・memoryless・操作的誤りを参照しない)、**A2 が converse の実体**。inventory file 自体は編集せず本計画側に注記 (planner editing boundary)。
7. **roadmap Ch.15 を converse-done にしない (要 orchestrator アクション)**: A1 完成をもって roadmap Ch.15 を「MAC converse 完成」と書いてはいけない (A1 は message-level のみ、A2 が残る)。roadmap reconcile (Ch.15 を converse-A2-pending と書く) は orchestrator が別途行う、本 planner は roadmap 不可侵。
8. **A2 は本親計画に直書き・別 child plan 不作成 + rename (要 orchestrator アクション)**: dangling ref `mac-converse-singleletterize-plan` (Converse.lean module docstring L23) は実在しない → A2 を本計画 (`mac-moonshot-plan.md`) の frontier として書き込めば足りるので **別 child plan は作らない**。orchestrator が (a) docstring L23 の ref を `mac-moonshot-plan.md` に向け直し、(b) `mac_converse` → `mac_converse_message_level` に rename (term-level consumer 0、blast radius 小、settled-facts 参照)。A2 で詰まった際の撤退 tag は `@residual(plan:mac-moonshot-plan)`。

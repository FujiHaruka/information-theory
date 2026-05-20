# T4-A Arithmetic Coding (Shannon-Fano-Elias) genuine discharge ムーンショット計画 🌙

> **Parent**:
> - [`arithmetic-coding-moonshot-plan.md`](./arithmetic-coding-moonshot-plan.md) §「撤退ライン L-AC1 / L-AC2 / L-AC3」
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. Arithmetic Coding」 (Cover-Thomas Ch.13.3, Shannon-Fano-Elias)
>
> **Inventory (必読、設計確定済)**: [`arithmetic-coding-inventory.md`](./arithmetic-coding-inventory.md)
> — 「期待長 sandwich + prefix-free 構成は full discharge 圏内、unique-decodable のみ Mathlib gap」と結論済。全 signature 検証済。
>
> **Predecessor / 再利用基盤** (publish 済、本 plan からは黒箱 reuse):
> - `Common2026/Shannon/ShannonCode.lean` — `entropyD`, `expectedLength`, `shannonLength`, `kraftSum`,
>   `entropyD_le_expectedLength_of_kraft` (`:164`, 源符号化下界), `expectedLength_shannon_lt_entropyD_add_one` (`:261`, Shannon 上界),
>   `shannonLength_kraft_le_one` (`:129`, Shannon 語長 Kraft 充足)
> - `Common2026/Shannon/ShannonCodeKraftReverse.lean` — `exists_prefix_code_of_kraft` (`:482`, Kraft 逆向き prefix code 構成, genuine),
>   `IsPrefixFree` (`:47`)
> - Mathlib `finTwoEquiv` (`Fin 2 ≃ Bool`), `List.prefix_map_iff_of_injective`, `List.length_map`, `List.map_injective`
>
> **Pattern 雛形**:
> - [`lz78-ziv-inequality-discharge-moonshot-plan.md`](./lz78-ziv-inequality-discharge-moonshot-plan.md) (同 T4-A の partial discharge plan、Status 実態整合行 / 規模見積 / 撤退ライン英字記号の流儀)
> - [`shannon-code-kraft-reverse-plan.md`](./shannon-code-kraft-reverse-plan.md) (再利用する `exists_prefix_code_of_kraft` の出自)
>
> **Goal (短形)**: 現 `Common2026/Shannon/ArithmeticCoding.lean` (288 行、完全 pass-through:
> opaque `codeword` field、3 述語 `Prop := True`、3 定理 body `:= h`) を **genuine 構成へ全面書き換え**。
> 任意 `c : ArithmeticCode α` ではなく **具体構成 `arithmeticCode P` / 具体語長 `sfeLength P`** に対する bound へ restate し、
> 期待長 sandwich `H₂(P) ≤ E[L] ≤ H₂(P) + 2` と prefix-free 性を **二進展開を完全回避** して full discharge。
> **0 sorry / 0 warning**、規模 ~150-220 行 (現 288 行の pass-through 置換)。
> 依存先は無い (`Common2026.lean:132` の import のみ) ため自由書き換え可。
>
> **撤退ライン (本 plan)**:
> [L-AC1 解除] cumulative-truncation `Prop := True` → prefix code を `exists_prefix_code_of_kraft` (整数 slot 構成) で genuine 構成 (実数二進展開を回避)。
> [L-AC2 解除] prefix-free 性 `Prop := True` → 構成した code の `IsPrefixFree` をそのまま結論。
> [L-AC3 解除] 期待長 `E[L] ≤ H+2` の identity wrap → ShannonCode 機構の線形 lift で full discharge。
> [L-AC4 新設・条件付き] unique-decodable: prefix-free ⟹ uniquely decodable は Mathlib に direct 補題なし。
>   Phase 6 が rabbit hole 化 (>80 行) したら honest brick として明示 signature pass-through で残す (撤退ライン詳細は §撤退ライン)。

## Status (2026-05-20)

> 実態整合 (2026-05-20): 親 `ArithmeticCoding.lean` は依然 PASS-THROUGH / FLAW-VACUOUS
> (headline `arithmetic_coding_expected_length_bounds` `:249` body `:= h_bound`、3 述語 `Prop := True`)。
> 本 discharge plan はその全面置換を企図。**Phase 0 起草中**。
> inventory (`arithmetic-coding-inventory.md`) で設計確定 (期待長 + prefix-free は full discharge 圏内、
> unique-decodable のみ Mathlib gap)、全 signature 検証済。

## 進捗

- [ ] Phase 0 — 設計確定 + 着手前 signature 再確認 (本 plan + inventory) 📋 → [arithmetic-coding-inventory.md](./arithmetic-coding-inventory.md)
- [ ] Phase 1 — `sfeLength` 定義 + skeleton (全定理 `:= by sorry`) 📋
- [ ] Phase 2 — `sfeLength_kraft_le_one` (Kraft 充足、半分計算) 📋
- [ ] Phase 3 — `arithmeticCode P` 具体構成 (`exists_prefix_code_of_kraft` + `finTwoEquiv` lift) 📋
- [ ] Phase 4 — `arithmeticCode_expected_length_bounds` 期待長 sandwich full discharge 📋
- [ ] Phase 5 — `arithmeticCode_prefix_free` full discharge 📋
- [ ] Phase 6 — `arithmeticCode_unique_decodable` (full genuine 試行 → 重ければ honest brick L-AC4) 📋
- [ ] Phase V — `Common2026.lean` import 確認 + clean check 📋

## ゴール / Approach

### 最終到達点 (Phase 6 完成形)

`Common2026/Shannon/ArithmeticCoding.lean` の主合流 (signature は inventory「genuine 目標」と整合):

```lean
/-- Shannon-Fano-Elias 語長: l(a) = ⌈-log₂ P(a)⌉ + 1. -/
noncomputable def sfeLength (P : Measure α) (a : α) : ℕ := shannonLength 2 P a + 1

/-- 期待長 sandwich (full discharge): H₂(P) ≤ E[L] ≤ H₂(P) + 2. -/
theorem arithmeticCode_expected_length_bounds
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a : α, 0 < P.real {a}) :
    entropyD 2 P ≤ expectedLength P (sfeLength P) ∧
      expectedLength P (sfeLength P) ≤ entropyD 2 P + 2 := ...

/-- prefix-free 構成 (full discharge): 長さ sfeLength の prefix-free な binary code が存在. -/
theorem arithmeticCode_prefix_free
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a : α, 0 < P.real {a}) :
    ∃ c : α → List Bool,
      (∀ a, (c a).length = sfeLength P a) ∧
      Function.Injective c ∧
      (∀ a b : α, a ≠ b → ¬ c a <+: c b) := ...
```

### Approach (overall strategy / shape of solution)

**核心**: genuine 化の唯一の構造変更は「任意 `c : ArithmeticCode α` を主語にするのをやめ、
**具体語長 `sfeLength P` / 具体構成 `arithmeticCode P` を主語にする**」こと。現状 flaw
(opaque length field が何にも紐づかない → sandwich は仮説なしには偽) は restate でしか
解消できない。restate さえ済めば、二進展開 (Mathlib gap) を一切経由せず既存 genuine 機構の
線形 lift で閉じる。

```
Cover-Thomas 13.3.3 (Shannon-Fano-Elias)
   │
   ├── [L-AC3 解除] 期待長 sandwich H ≤ E[L] ≤ H+2 ── full discharge (Phase 2,4)
   │     ├ 下界 H ≤ E[L]:  entropyD_le_expectedLength_of_kraft (既存) を sfeLength に直適用
   │     │                  (前提: sfeLength も Kraft 充足 ← Phase 2)
   │     └ 上界 E[L] ≤ H+2: E[L_sfe] = E[L_shannon] + 1  (∑ 線形性 + ∑P=1)
   │                         < (H+1) + 1 = H+2           (expectedLength_shannon_lt_entropyD_add_one, 既存)
   │
   ├── [L-AC1+L-AC2 解除] prefix-free 構成 ── full discharge (Phase 3,5)
   │     ├ exists_prefix_code_of_kraft (D=2, l=sfeLength) → c : α → List (Fin 2)  ← 整数 slot 構成 (実数二進展開を回避)
   │     └ finTwoEquiv lift: codeword a := (c a).map ⇑finTwoEquiv : List Bool
   │         length 保存  : List.length_map
   │         prefix-free 保存 : List.prefix_map_iff_of_injective finTwoEquiv.injective
   │         injective 保存 : List.map_injective + finTwoEquiv.injective
   │
   └── [L-AC4 条件付き] unique-decodable ── full 試行 → 重ければ honest brick (Phase 6)
         prefix-free ⟹ uniquely decodable は Mathlib に direct 補題なし
         (kraft_mcmillan は逆向き)。撤退ラインを明示 signature pass-through に縮退。
```

**設計の核**: `sfeLength P a := shannonLength 2 P a + 1` という **length 関数だけ**定義すれば、
期待長 sandwich は ShannonCode 機構 (`entropyD_le_expectedLength_of_kraft` +
`expectedLength_shannon_lt_entropyD_add_one`) で閉じる。**符号語の構成も二進展開も期待長証明には不要**。
prefix-free は別途 `exists_prefix_code_of_kraft` (既存 genuine、整数 slot 構成) を D=2 で叩き、
返る `List (Fin 2)` を `finTwoEquiv` で `List Bool` に持ち上げるだけ。当初の懸念「実数 F̄ の
二進展開が Mathlib gap」は整数 slot 構成で完全に回避される。

**Mathlib-shape-driven の設計選択**: `sfeLength` の **整数 +1 形** (`shannonLength + 1`) を採る。
- `entropyD_le_expectedLength_of_kraft` は「任意 `l : α → ℕ` で Kraft 充足のみ前提」→ sfeLength に直適用可。
- `exists_prefix_code_of_kraft` は `l : α → ℕ`, `hl : ∀ a, 0 < l a` を要求 → `+1` で `0 < sfeLength` が自明。
- 教科書 literal の「実数中点 F̄(a) の二進展開」形は **意図的に書かない** (それは Mathlib gap、
  かつ slot 構成と同じ prefix-free code を与えるので genuine 性に不要)。教科書同値性は Phase 外。

**restate に伴う signature 変更 (不可避)**:
主定理は full-support 仮定 `hP : ∀ a, 0 < P.real {a}` を取る (Cover-Thomas の暗黙仮定、
既存 Shannon 定理 `expectedLength_shannon_lt_entropyD_add_one` と同形)。任意 `c` 引数は廃し
具体構成を主語にする。`ArithmeticCode` structure 自体は残してよい (`arithmeticCode P : ArithmeticCode α`
を構成 def として与えてもよいし、prefix-free を `∃ c : α → List Bool` の存在形で返してもよい
— inventory「genuine 目標」は存在形を採用。実装時にどちらが下流から呼びやすいか確認)。

### 規模見積

| Phase | 中央 | 出力 | proof-log |
|---|---|---|---|
| Phase 1 | **30 行** | `sfeLength` 定義 + 全定理 skeleton (`:= by sorry`)、imports、namespace | no |
| Phase 2 | **20 行** | `sfeLength_kraft_le_one` (各項 `2^(-(l+1)) = 2^(-l)/2 ≤ 2^(-l)` の Σ) | no |
| Phase 3 | **35 行** | `arithmeticCode P` 構成 (`exists_prefix_code_of_kraft` + `finTwoEquiv` lift) | no |
| Phase 4 | **45 行** | `arithmeticCode_expected_length_bounds` 期待長 sandwich | yes |
| Phase 5 | **15 行** | `arithmeticCode_prefix_free` (Phase 3 の構成をそのまま結論) | no |
| Phase 6 | **40-80 行 / 撤退時 ~15 行** | `arithmeticCode_unique_decodable` (full or honest brick) | yes |
| Phase V | **0-1 行** | `Common2026.lean` import 確認 (既に line 132 にある、変更不要) | no |
| **累計** | **~150-220 行** | 1 ファイル全面置換 | — |

### ファイル構成

```
Common2026/Shannon/
  ArithmeticCoding.lean   ← 現 288 行 (pass-through) を全面置換 (~150-220 行 genuine)
                            ・sfeLength 定義
                            ・sfeLength_kraft_le_one
                            ・arithmeticCode 具体構成 (or 存在形)
                            ・arithmeticCode_expected_length_bounds (full discharge)
                            ・arithmeticCode_prefix_free (full discharge)
                            ・arithmeticCode_unique_decodable (full or honest brick L-AC4)
Common2026.lean           ← import は既に line 132 にある (変更不要)
```

## Phase 0 - 設計確定 + 着手前 signature 再確認 📋

inventory で設計確定済。**着手前に必ず実装者が確認する事項** (signature drift / 仮定漏れ防止):

- [ ] `shannonLength_kraft_le_one` (`ShannonCode.lean:129`) の **正確な hP 仮定の有無** を実装前に確認。
      inventory は `entropyD_le_expectedLength_of_kraft` の hP 必須 (full support) は記録済だが、
      `shannonLength_kraft_le_one` 側の hP (full-support `∀ a, 0 < P.real {a}` を取るか否か) は未確定。
      `sfeLength_kraft_le_one` を Shannon 版から sandwich する際に必要な仮定が変わる。
- [ ] `finTwoEquiv` の正確な declaration 名・向き (`Fin 2 ≃ Bool` で確定、inventory B5)。`⇑finTwoEquiv` の coe 形を loogle で再確認。
- [ ] `List.map` 下の prefix 否定保存補題の正確名: 候補 `List.prefix_map_iff_of_injective` (inventory B2 で `Init/Data/List/Nat/Sublist.lean:141` と検証済)。
      `¬ (c a) <+: (c b)` の否定保存に使えるか (iff なので両向き OK) を実装時に loogle/rg で再確認。
- [ ] `exists_prefix_code_of_kraft` の `hk` 引数の正確な形 (`∑ a, (D:ℝ)^(-(l a:ℤ)) ≤ 1` = `kraftSum (D:ℝ) l` の unfold)。
      `D = (2:ℕ)` 適用時の `(2:ℕ)` ↔ `(2:ℝ)` cast を `sfeLength_kraft_le_one` (`kraftSum 2` 形) から橋渡しする経路を確認。
- [ ] full-support 仮定 `hP` の表記が既存 Shannon 定理と完全一致 (`∀ a : α, 0 < P.real {a}`) であること。

## Phase 1 - `sfeLength` 定義 + skeleton 📋

skeleton-driven (CLAUDE.md): 全定理を `:= by sorry` で並べ、namespace / imports / variable を確定。

- [ ] imports: `Common2026.Shannon.ShannonCode`, `Common2026.Shannon.ShannonCodeKraftReverse`,
      `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`, `Mathlib.Logic.Equiv.Defs`。`import Mathlib` 禁止。
- [ ] namespace `InformationTheory.Shannon.ArithmeticCoding`、`open` で再利用補題を引き込む
      (inventory「着手 skeleton」line 356-363 のテンプレート踏襲)。
- [ ] `variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`。
- [ ] `noncomputable def sfeLength (P : Measure α) (a : α) : ℕ := shannonLength 2 P a + 1`。
- [ ] 全定理 (`sfeLength_kraft_le_one` / 構成 / sandwich / prefix-free / unique-decodable) を `:= by sorry` で stub。
- [ ] **検証**: skeleton が type-check (sorry warning のみ) すること。LSP `<new-diagnostics>` を待つ。
- **撤退ライン**: なし (定義 + stub のみ、確実)。

## Phase 2 - `sfeLength_kraft_le_one` 📋

`kraftSum 2 (sfeLength P) ≤ 1` を示す。鍵は半分計算。

- [ ] 各項書換: `(2:ℝ)^(-(↑(shannonLength 2 P a + 1):ℤ)) = (2:ℝ)^(-(↑(shannonLength 2 P a):ℤ)) / 2`。
      `zpow` の `-(n+1) = -n - 1` 分解 → `zpow_sub` / `zpow_neg_one` (ShannonCode 内の `zpow_neg_natCast_eq_rpow` `:93` 系を参照)。
- [ ] Σ 線形性: `kraftSum 2 (sfeLength P) = (1/2) * kraftSum 2 (shannonLength 2 P)` (`Finset.sum_div` / `Finset.mul_sum`)。
- [ ] `kraftSum 2 (shannonLength 2 P) ≤ 1` を `shannonLength_kraft_le_one` で得る (Phase 0 の hP 確認結果に依存)。
- [ ] 結論: `(1/2) * (≤1) ≤ 1/2 ≤ 1`。
- **依存補題**: `shannonLength_kraft_le_one` (`ShannonCode.lean:129`), `kraftSum` (`:59`), `zpow_sub` 系。
- **撤退ライン**: 半分計算が `zpow` cast で詰まったら、項ごとの `≤` (`2^(-(l+1)) ≤ 2^(-l)`) を `Finset.sum_le_sum` で集約する **monotone 経路** に切替 (等式不要、`≤ Σ 2^(-l) ≤ 1`)。これでも full discharge。

## Phase 3 - `arithmeticCode P` 具体構成 📋

`exists_prefix_code_of_kraft` で genuine prefix code を取り、`List Bool` に lift。

- [ ] `exists_prefix_code_of_kraft (D := 2) (by norm_num : (2:ℕ) ≤ 2) (sfeLength P) hl hk` を適用。
      - `hl : ∀ a, 0 < sfeLength P a` は `shannonLength + 1 ≥ 1` で `Nat.succ_pos` / `Nat.lt_add_one_iff` 自明。
      - `hk : ∑ a, (2:ℝ)^(-(sfeLength P a:ℤ)) ≤ 1` は `sfeLength_kraft_le_one` (Phase 2) を `kraftSum` unfold して供給。cast 橋渡し (Phase 0)。
- [ ] 得た `c : α → List (Fin 2)` (+ injective + length=sfeLength + IsPrefixFree) を分解。
- [ ] lift: `codeword a := (c a).map ⇑finTwoEquiv : α → List Bool`。
      - length 保存: `List.length_map` → `(codeword a).length = sfeLength P a`。
      - injective 保存: `List.map_injective finTwoEquiv.injective` + 元 c の injective。
      - prefix-free 保存: `List.prefix_map_iff_of_injective finTwoEquiv.injective` で `¬ ... <+:` を移送。
- [ ] 構成を Phase 5 (prefix-free) / Phase 6 (unique-decodable) が再利用できる形で公開
      (private helper or 補助 lemma `arithmeticCode_spec` として「length=sfeLength ∧ injective ∧ prefix-free」をまとめて返す)。
- **依存補題**: `exists_prefix_code_of_kraft` (`ShannonCodeKraftReverse.lean:482`), `finTwoEquiv`,
      `List.length_map`, `List.map_injective`, `List.prefix_map_iff_of_injective`。
- **撤退ライン**: `prefix_map_iff_of_injective` の正確名 / 向きが合わなければ `List.IsPrefix.map` (forward) の対偶で代用、
      または `c a = c b → ...` の injective から prefix 否定を手で導く (~10 行追加)。いずれも full discharge 圏内。

## Phase 4 - `arithmeticCode_expected_length_bounds` 期待長 sandwich 📋

`entropyD 2 P ≤ expectedLength P (sfeLength P) ∧ expectedLength P (sfeLength P) ≤ entropyD 2 P + 2`。

- [ ] **線形性補題**: `expectedLength P (sfeLength P) = expectedLength P (shannonLength 2 P) + 1`。
      `∑ P(a)·(↑(l a)+1) = ∑ P(a)·↑(l a) + ∑ P(a) = E[L_sh] + 1` (`Nat.cast_add`, `Finset.sum_add_distrib`,
      `mul_add`, `∑ P(a) = 1` via `sum_measureReal_singleton` — ShannonCode 内に既出パターン)。
- [ ] **下界** `entropyD 2 P ≤ E[L_sfe]`: `entropyD_le_expectedLength_of_kraft (by norm_num : (1:ℝ)<2) P hP (sfeLength P) (sfeLength_kraft_le_one ...)` 直適用。
- [ ] **上界** `E[L_sfe] ≤ entropyD 2 P + 2`: 線形性で `E[L_sfe] = E[L_sh] + 1`、
      `expectedLength_shannon_lt_entropyD_add_one (by norm_num) P hP : E[L_sh] < H+1` を `+1` して `E[L_sfe] < (H+1)+1 = H+2` → `le_of_lt`。
- [ ] `⟨下界, 上界⟩` で結論。
- **依存補題**: `entropyD_le_expectedLength_of_kraft` (`:164`), `expectedLength_shannon_lt_entropyD_add_one` (`:261`),
      `sfeLength_kraft_le_one` (Phase 2), `sum_measureReal_singleton` (Mathlib, ShannonCode 内既出)。
- **proof-log: yes** — 線形性補題の cast / Σ 展開で詰まりやすい (`Nat.cast_add` 後の `mul_add` 分配、`∑ P(a)=1` の正確な補題名)。判断は proof-log に残す。
- **撤退ライン**: 線形性等式が重ければ、下界は sfeLength 直適用 (Kraft 充足のみ前提なので不変)、
      上界のみ「`E[L_sfe] ≤ E[L_sh] + 1 < H+2`」を項別 `Finset.sum_le_sum` + `Nat.ceil_lt_add_one` で再構成。**full discharge 維持**。

## Phase 5 - `arithmeticCode_prefix_free` 📋

- [ ] Phase 3 の構成 (`arithmeticCode_spec` or 存在形 `∃ c`) をそのまま結論。
      存在形なら `⟨codeword, length 保存, injective, prefix-free⟩` を返すだけ。
- **依存**: Phase 3 の成果。
- **撤退ライン**: なし (Phase 3 が通れば自明)。

## Phase 6 - `arithmeticCode_unique_decodable` 📋

prefix-free ⟹ uniquely decodable。Mathlib に prefix→UD direct 補題なし (inventory B6: `kraft_mcmillan` は逆向き)。

**段階方針 (full 試行 → 撤退判定)**:

- [ ] **full 試行**: 一般補題 `IsPrefixFree c → (∀ s₁ s₂, (s₁.map c).flatten = (s₂.map c).flatten → s₁ = s₂)` を証明。
      greedy decode の単射性を `flatten` の最短 prefix 一意性で帰納 (List 長さ induction、prefix-free から
      最初のブロックが一意に切り出せる)。Mathlib `UniquelyDecodable` (`List (List α)` 形) への橋を張るか、
      結論を直接 `flatten` injective 形で書くか実装時選択。
- [ ] **撤退判定**: 上記が **推定 >80 行 / rabbit hole 化**したら **honest brick L-AC4 として分離**。
      `arithmeticCode_unique_decodable` を「prefix-free 仮定 (genuine、Phase 3/5 の出力) を受けて
      unique-decodable 結論を返す」明示 signature pass-through で残す。`Prop := True` は使わない
      (honest hypothesis pass-through、`:= h_pf_real` ではなく **genuine な prefix-free 補題を仮定として明示**)。
      docstring に「prefix-free から従う標準事実 (Cover-Thomas 5.2.2)、別 brick で discharge 予定」と明記。
- **依存補題**: (full 時) `List.flatten`, `List.IsPrefix` 系, prefix-free 帰納。(撤退時) Phase 3/5 の prefix-free 出力。
- **proof-log: yes** — full / 撤退の判断点、greedy decode 帰納の詰まり所を記録。
- **撤退ライン [L-AC4 新設]**: full 化が 80 行超 or 1 セッション内に閉じない見込みなら honest brick に縮退。
      **期待長 (Phase 4) + prefix-free (Phase 5) は full genuine 確定**、unique-decodable のみ honest pass-through
      という段階的着地が現実的 (inventory §撤退ラインへの距離と整合)。

## Phase V - `Common2026.lean` 編入 + clean check 📋

- [ ] `Common2026.lean:132` の `import Common2026.Shannon.ArithmeticCoding` は既存 (file 名不変のため変更不要、確認のみ)。
- [ ] `lake env lean Common2026/Shannon/ArithmeticCoding.lean` silent (0 error / 0 sorry / 0 warning)。
- [ ] signature restate (任意 `c` → 具体構成) により旧 caller が壊れていないことを確認
      (依存先は無い旨を inventory が記録、`rg "arithmetic_coding_"` で横断確認)。

## 撤退ライン

- **L-AC1 (解除)**: cumulative-truncation。`exists_prefix_code_of_kraft` (整数 slot 構成、既存 genuine) で
  prefix code を構成 → 実数二進展開 (Mathlib gap) を完全回避。当初撤退理由「実数 F̄ 二進展開が gap」は無効化。
- **L-AC2 (解除)**: prefix-free 性。Phase 3 構成の `IsPrefixFree` を `finTwoEquiv` lift して結論 (Phase 5)。
- **L-AC3 (解除)**: 期待長 `H ≤ E[L] ≤ H+2`。ShannonCode 機構の線形 lift で full discharge (Phase 2,4)、二進展開不要。
- **L-AC4 (新設・条件付き発動)**: unique-decodable。prefix-free ⟹ UD は Mathlib に direct 補題なし。
  Phase 6 の full 化が >80 行 / 行き詰まったら **honest hypothesis pass-through** (genuine な prefix-free 補題を
  明示 signature で仮定、`Prop := True` は使わない) に縮退。期待長 + prefix-free は full genuine を維持。

## 当面の next step

1. Phase 0 着手前確認 (`shannonLength_kraft_le_one` の hP 仮定、`finTwoEquiv` coe、prefix-map 補題名、cast 橋)
2. Phase 1 skeleton (全定理 `:= by sorry`) → type-check 確認
3. Phase 2 → Phase 3 → Phase 4 → Phase 5 を順に full discharge
4. Phase 6 full 試行 → 撤退判定 (L-AC4) → Phase V clean check

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 起草時点の確定事項 (実装中の方針変更があればここに追記):
1. **restate を採用 (任意 c → 具体構成)**: 現 pass-through の core flaw (opaque length field が
   構成に紐づかず sandwich が仮説依存) は restate でしか解消できない。`ArithmeticCode` structure は
   残してよいが、主定理の主語は `sfeLength P` / `arithmeticCode P` に変更。full-support `hP` を追加
   (既存 Shannon 定理と同形、不可避)。
2. **二進展開を回避**: inventory の最重要発見 (`exists_prefix_code_of_kraft` の整数 slot 構成が
   実数二進展開を不要にする) を全面採用。教科書 literal の中点二進展開は Phase 外。
-->

# T1-A' Huffman 最適性 (sibling property + 任意 `l` 比較) ムーンショット計画 🌙

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A'. Huffman 最適性 (sibling property + 任意 `l` 比較)」
> - 先行 (T1-A 完了): [`huffman-moonshot-plan.md`](./huffman-moonshot-plan.md) (本 plan からは archive 扱いの参照のみ、更新しない)
>
> **Inventory**: [`huffman-optimality-mathlib-inventory.md`](./huffman-optimality-mathlib-inventory.md)
>
> **先行実装 (T1-A 完了、不変として再利用)**:
> - `Common2026/Shannon/Huffman.lean` (953 行 / 0 sorry) — `huffmanLength`, `huffmanLengthAux`,
>   `huffmanStep` (Subtype + `HuffmanGrouping` invariant), `huffmanLengthAux_eq_step`,
>   `huffmanLengthAux_step_merged`, `huffmanLengthAux_step_other`, `huffmanLengthAux_const_on_group`,
>   `huffmanLength_pos`, `huffmanLength_kraft_le_one`, `exists_huffman_prefix_code`.
> - `Common2026/Shannon/ShannonCode.lean` (`expectedLength`, `kraftSum`,
>   `entropyD_le_expectedLength_of_kraft`).
> - `Common2026/Shannon/ShannonCodeKraftReverse.lean` (`IsPrefixFree`, `exists_prefix_code_of_kraft`).
>
> Cover & Thomas *Elements of Information Theory* 2nd ed. **Theorem 5.8.1** (Huffman optimality)
> 主定理 (任意 Kraft-feasible 語長関数 `l` との比較形) の formalization。T1-A で publish 済の
> `huffmanLength` を主役、sibling property (Lemma 5.8.1) を intermediate lemma 化し、
> `Fintype.card α` 上の strong induction で `n → n-1` 縮約を回す。

## Status (2026-05-19)

> 実態整合 (2026-05-20): DONE-HONEST-HYPS — 主定理 `huffmanLength_optimal_with_hypotheses` (`Common2026/Shannon/HuffmanOptimality.lean:1041`) は 2 つの **genuine analytic Prop hypothesis** (`SwapNormalizationHypothesis` `:759`、`HuffmanMergedIdentificationHypothesis` `:776` — どちらも `∀…∃…` の実質 Prop で `:= True` ではない) を引数で受けて `expectedLength P (huffmanLength P) ≤ expectedLength P l` を 0 sorry で証明。`exists_sibling_min_pair` (`:227`) も 0 sorry publish 済 (ただし判断ログ #2 で最深性条項は削除済)。hypothesis 引数なしの強形 `huffmanLength_optimal` は **未 publish** (全 variant が hypothesis を保持、T1-A'' へ)。pass-through (`Prop := True`) は不在。

**T1-A' weak form publish ✅** — `huffmanLength_optimal_with_hypotheses` (case Y、0 sorry) を
`Common2026/Shannon/HuffmanOptimality.lean` (1054 行) で publish。`Huffman.lean` に
`huffmanLength_kraft_eq_one` (+14 行) を副産物として publish。**完全形 (hypothesis 2 件 discharge)**
は後継 seed **T1-A''** に分離: `SwapNormalizationHypothesis` (Cover-Thomas Lemma 5.8.1 (i)
Kraft = 1 shortening 込み swap normalization、~150-200 行) + `HuffmanMergedIdentificationHypothesis`
(α/α' structural correspondence、~150-200 行)。判断ログ #2-#7 参照。

## 進捗

- [ ] Phase 0 — Mathlib 在庫再確認 + Subtype `α'` 型クラス継承の確認 📋
- [ ] Phase 1 — skeleton (`HuffmanOptimality.lean` 新規ファイル、全 sorry) 📋
- [ ] Phase 2 — `exists_sibling_min_pair` (Cover-Thomas Lemma 5.8.1) 📋
- [ ] Phase 3 — `α'` Subtype lift bridges (merged measure + bridge L + bridge R) 📋
- [ ] Phase 4 — 主定理 `huffmanLength_optimal` (`n → n-1` induction 合成) 📋
- [ ] Phase 5 — verify + regression check 📋

## ゴール / Approach

### Goal (最終定理 signature)

```lean
-- 新規ファイル `Common2026/Shannon/HuffmanOptimality.lean` で publish
namespace InformationTheory.Shannon.Huffman

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Sibling property (Cover-Thomas Lemma 5.8.1)** — intermediate lemma. -/
theorem exists_sibling_min_pair
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) :
    ∃ a b : α, a ≠ b ∧ huffmanLength P a = huffmanLength P b ∧
      (∀ c, huffmanLength P c ≤ huffmanLength P a) ∧
      (∀ c, P.real {a} ≤ P.real {c} ∨ P.real {b} ≤ P.real {c})

/-- **主定理 (Cover-Thomas Theorem 5.8.1)** — 任意 Kraft-feasible `l` 比較形. -/
theorem huffmanLength_optimal
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l

end InformationTheory.Shannon.Huffman
```

### Approach (overall strategy / shape of solution)

**戦略の shape**: T1-A で publish 済の `huffmanLength` / `huffmanLengthAux` /
`huffmanLengthAux_step_merged` / `huffmanLengthAux_step_other` / `huffmanLengthAux_const_on_group`
を **黒箱 reuse** し、ファイルとしては独立した `HuffmanOptimality.lean` で sibling property +
主定理を 2 段で publish。T1-A の `Huffman.lean` は **不変** (1000 行越え回避、953 行のまま温存)。

**抽象水準の最終 commitment** (inventory §H 推奨設計、ハイブリッド):

1. **§F-2 (i) Subtype `α' := { x : α // x ≠ b }`** を merged 型として採用。Mathlib type-class
   `[Fintype α']` / `[DecidableEq α']` / `[MeasurableSpace α']` / `[MeasurableSingletonClass α']` の
   auto-derive を頼り、**Quotient 経路は撤退ラインで言及するに留め採用しない** (撤退ライン §G-2)。
2. **§F-3 (ii) `α` 型不変経路**を主たる induction motor とする。すなわち主定理 induction は
   `Fintype.card α` 上の `Nat.strong_induction_on` で回すが、IH 適用時に **`α' := { x : α // x ≠ b }`
   上で再帰呼び出し**し、T1-A の `huffmanLength` ( `Measure α' → α' → ℕ`) と
   T1-A 既存 step lemma を `α'` 側でも instantiation して使う。`huffmanLengthAux` 内部の
   `Multiset (Finset α × ℝ)` 表現は **`α` 側 / `α'` 側それぞれの induction step の中で個別に展開**
   され、cross-type bridge は Phase 3 の lift lemma 群が引き受ける。
3. **§F-4 (b) `Nat.strong_induction_on`** を induction tactic に採用。
   `induction hn : Fintype.card α using Nat.strong_induction_on generalizing α P l ...`
   pattern (T1-A 既存 `huffmanLengthAux_pos_of_mem` / `huffmanLengthAux_const_on_group` の
   `s.card` 上 strong induction と同 motif、Phase 0 で type-class generalizing の挙動を確認)。

**4 段の論理展開**:

1. **Sibling property (Phase 2)** を Cover-Thomas Lemma 5.8.1 の standard form で取る:
   ∃ a b, a ≠ b, `huffmanLength P a = huffmanLength P b`, 共に最深 leaf, かつ 2 element の
   確率が最小ペア。T1-A 既存 `huffmanLengthAux_const_on_group` (同一 group 上で `huffmanLengthAux`
   定数) + `huffmanStep_spec` (huffmanStep が最小 2 element を確定的に取り出す) + `Equiv.swap`
   ベースの swap argument で構成 (inventory §B/§C 既存 API)。
2. **Merged measure `P'` 構成 + Subtype lift (Phase 3)**: `α' := { x : α // x ≠ b }` 上で
   `P'.real {⟨x, _⟩} := if x = a then P.real {a} + P.real {b} else P.real {x}` を **point-mass
   形式**で構成 (`Measure.real` 経由)、`IsProbabilityMeasure P'` を `Finset.sum` 等式で確立。
3. **Bridge L / Bridge R (Phase 3)**: Huffman 側と任意 `l` 側それぞれで「`α` 上 expectation =
   `α'` 上 expectation + (P{a} + P{b})」の等式 / 不等式を出す。Bridge L は等式
   (T1-A `huffmanLengthAux_step_merged` + `huffmanLengthAux_step_other` の直接 reuse)、
   Bridge R は不等式 (sibling property で normalize した `l` に対する +1 ペナルティ計算)。
4. **主定理合成 (Phase 4)**: IH (`α'` 上の `huffmanLength_optimal`) + Bridge L + Bridge R の
   3 段不等式を `Nat.strong_induction_on` で合成。base case (`Fintype.card α ≤ 1`) は
   `huffmanLength = 0` (T1-A 既存 `huffmanLengthAux_eq_zero` 系) で trivial。

**Bridge と既存資産の関係**:

- T1-A 既存 `huffmanLength` / `huffmanLengthAux` / step lemma は **不変、API 変更なし**。Phase 3
  bridge lift は T1-A 既存 step lemma を `α'` 側で instantiation する形で再利用 (cross-type
  bridge ~80 行で済む見込み、§規模見積)。
- `Subtype` 経路の type-class 継承は Mathlib auto-derive で原則無償 (`Subtype.fintype` /
  `Subtype.decidableEq` / `Subtype.instMeasurableSpace`)。**唯一の手作業箇所**は
  `MeasurableSingletonClass α'` の継承 (Phase 0 で確認、inventory §F 「主要前提条件ボックス」)。
- `Quotient` 経路は撤退ライン §G-2 で言及するのみ。**採用しない**。

### 規模見積もり (既存 step lemma 再利用カウントの根拠)

| Phase | 内容 | 行数 |
|---|---|---|
| 0 | Mathlib 在庫再確認 + 型クラス継承 | 0 |
| 1 | skeleton (全 sorry) | ~50 |
| 2 | `exists_sibling_min_pair` (helper 含む) | ~150 |
| 3 | Subtype `α'` lift bridges (merged measure + Bridge L + Bridge R) | ~250 |
| 4 | 主定理 `huffmanLength_optimal` (induction 合成) | ~100 |
| 5 | verify + regression | 0 |
| **合計** | | **~500 行** |

**500 行収束の根拠 (既存 step lemma 再利用)**:

inventory §A で publish 済の T1-A API のうち、**Phase 3 bridge L で `huffmanLengthAux_step_merged`
(11 行 verbatim 再利用) + `huffmanLengthAux_step_other` (11 行 verbatim 再利用) を `α' ` 側で
再 instantiation するだけで Bridge L の +1 ペナルティ計算が full discharge** される。これと
Phase 2 sibling property での `huffmanLengthAux_const_on_group` の再利用 (1 件、~30 行節約) で、
inventory §「自作見積」が出していた ~725 行 (Subtype 路線、型変化あり) のうち
**約 225 行が T1-A 既存 API 再利用で消える**見込み (~725 → ~500)。inventory §H 1 行サマリの
「~500 行で完成」の見積根拠と一致。

撤退ライン §G-1 (~700+) を超える兆候が現れた時点で **判断ログに記録 + lean-planner 再相談**
(本 plan §判断ログにエントリ枠を確保、起草時 #0)。

## 設計判断 (確定事項)

C-1〜C-4 は計画起草時 (2026-05-19) の確定。Phase 0 / Phase 3 着手時の発見で覆る場合は
判断ログに append。

### C-1. 抽象水準 — **Subtype `α'` + 型不変 induction + `Nat.strong_induction_on` のハイブリッド**

(inventory §H 推奨設計、§F-2 (i) + §F-3 (ii) + §F-4 (b) の組み合わせ)

- **§F-2 (i)** merged 型は `α' := { x : α // x ≠ b }` Subtype を採用。
- **§F-3 (ii)** 主 induction motor は `α` 型不変、`Fintype.card α` 上の strong induction。IH 適用時に
  `α'` で recursive call。
- **§F-4 (b)** `Nat.strong_induction_on` を induction tactic に採用、T1-A 既存 pattern と一致。

**理由**: inventory §H「推奨設計 (1 行サマリ)」に従う。Quotient 経路 (§F-2 (ii)) を取ると
`MeasurableSpace (Quotient s)` 自前 `comap` 構成 + `MeasurableSingletonClass` 自前付与
で ~50-80 行の type-class 地獄に陥り撤退ライン §G-2 発動リスク。Subtype 路線なら Mathlib
auto-derive で原則無償。

### C-2. Sibling property の statement form — **inventory §F-1 候補 (a) 統合形を採用**

```lean
theorem exists_sibling_min_pair
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) :
    ∃ a b : α, a ≠ b ∧ huffmanLength P a = huffmanLength P b ∧
      (∀ c, huffmanLength P c ≤ huffmanLength P a) ∧
      (∀ c, P.real {a} ≤ P.real {c} ∨ P.real {b} ≤ P.real {c})
```

(inventory §F-1 候補 (a) 採用、(b) 分離形は不採用)

**理由**: 主定理 induction step で 1 件取り出せばよい。Cover-Thomas Lemma 5.8.1 (i) (最深 leaf
と最小確率の swap 可) / (ii) (最深 leaf の兄弟も最深) は **`exists_sibling_min_pair` の内部
helper として `private theorem` で抽出**する (Phase 2.1, 2.2 で扱う) — 統合 lemma を
publish 面に持ち、内部分解は private に閉じる。

### C-3. Merged measure `P'` の構成 — **point-mass 直接構成、`Measure.map` / `Measure.restrict` 経由しない**

```lean
-- Phase 3 で publish 予定 (sketch)
noncomputable def mergedMeasure (P : Measure α) (a b : α) (hab : a ≠ b) :
    Measure { x : α // x ≠ b } :=
  ... (point-mass 直接構成)

lemma mergedMeasure_real (P : Measure α) (a b : α) (hab : a ≠ b) (x : { x : α // x ≠ b }) :
    (mergedMeasure P a b hab).real {x} =
      if x.val = a then P.real {a} + P.real {b} else P.real {x.val}
```

**理由**: `Measure.map (Subtype.val) P` 経由は `P` の `MeasurableSet` 構造を 1 step 経由する
オーバーヘッドが ~30-50 行、かつ point-mass `P.real {a} + P.real {b}` の merged 性質を取り出すのに
追加 bridge 補題が必要。**point-mass 形式の直接構成 (Mathlib `MeasureTheory.Measure.dirac` の
finite sum 形** ~30 行) で **bridge 一段で済む**。Phase 3.1 で確定。

### C-4. 撤退ライン発動の事前枠 — **判断ログにエントリ #0 を起草時点で予約**

inventory §G-1 (~700+ 規模超過)、§G-2 (Subtype type-class 地獄)、§G-3 (sibling swap argument
5 ターン進まない) のいずれかが発動した場合、**判断ログに append**し lean-planner / proof-pivot-advisor
再相談に回す枠を予約する。

T1-A 判断ログ #2-#4 の経験から、**「単一セッションで 0 sorry を狙わず、Phase 2 / Phase 3 で
それぞれ別セッションを使い切る」設計** を default とし、規模超過の判定は **2 セッション目
入った時点**で初めて発動を検討する (1 セッション内で発動禁止)。

## File / module layout

### 新規ファイル: `Common2026/Shannon/HuffmanOptimality.lean`

import 一覧 (inventory §「着手 skeleton」+ §C/§D/§E/§F の Mathlib path verbatim):

```lean
import Mathlib.Logic.Equiv.Basic              -- Equiv.swap
import Mathlib.Logic.Function.Basic           -- Function.update
import Mathlib.Data.Finset.Max                -- Finset.exists_max_image / exists_min_image
import Mathlib.Data.Finset.Image              -- Finset.image_erase
import Mathlib.Data.Fintype.EquivFin          -- Fintype.equivOfCardEq (alt)
import Mathlib.Algebra.BigOperators.Group.Finset.Basic  -- sum_pair / mul_prod_erase / sum_attach / sum_image
import Mathlib.MeasureTheory.Measure.Real     -- Measure.real (継承)
import Common2026.Shannon.Huffman             -- T1-A 既存 API 全件
```

**根拠**:
- `Logic.Equiv.Basic`: `Equiv.swap` / `swap_apply_left` / `swap_apply_right` /
  `swap_apply_of_ne_of_ne` (任意 `l` の swap 正規化、inventory §C).
- `Logic.Function.Basic`: `Function.update` / `update_self` / `update_of_ne` (alt: 1 点書き換え、
  inventory §C).
- `Finset.Max`: `Finset.exists_max_image` / `Finset.exists_min_image` (最深 leaf / 最小確率
  取り出し、inventory §B).
- `Finset.Image`: `Finset.image_erase` (Subtype `α'` への bridge、inventory §E).
- `Fintype.EquivFin`: `Fintype.equivOfCardEq` (alt 経路、IH を `Fin (n-1)` で書き戻す場合、
  inventory §F).
- `BigOperators.Group.Finset.Basic`: `Finset.sum_pair` / `Finset.mul_prod_erase` /
  `Finset.sum_attach` / `Finset.sum_image` / `Finset.sum_subtype_of_mem` (Bridge L/R 計算、
  inventory §D).
- `MeasureTheory.Measure.Real`: `Measure.real` (Subtype 上の measure 構成、
  `[MeasurableSingletonClass α']` 継承確認、inventory §F).
- `Common2026.Shannon.Huffman`: T1-A 既存 API (`huffmanLength`, `huffmanLengthAux`,
  `huffmanStep`, `huffmanLengthAux_step_merged`, `huffmanLengthAux_step_other`,
  `huffmanLengthAux_const_on_group`, `HuffmanGrouping` etc.) 全件 reuse.

**`Common2026.lean` への追加**:

```diff
 import Common2026.Shannon.Huffman
+import Common2026.Shannon.HuffmanOptimality
```

`Huffman.lean` 直後に挿入予定 (Phase 1 で具体位置確定)。

## Phase 0 — Mathlib 在庫再確認 + Subtype `α'` 型クラス継承の確認 📋

在庫 (`huffman-optimality-mathlib-inventory.md`) 作成時 (2026-05-19) の前提を実機 (loogle +
`lake env lean` 1 行 probe) で確認する gap-check 1 ターン。**特に C-1 の Subtype 路線が
要求する 4 つの type-class 継承を全て確認** することが本 Phase の核心。

- [ ] **0.1** `loogle "Equiv.swap"` で `Mathlib.Logic.Equiv.Basic` の swap signature 確認
  (inventory §C 既出、再確認のみ).
- [ ] **0.2** `loogle "Finset.exists_max_image"` で `Mathlib/Data/Finset/Max.lean:525` 確認
  (inventory §B 既出).
- [ ] **0.3** `loogle "Finset.mul_prod_erase, Finset.sum_pair"` で additive variant 確認
  (inventory §D 既出).
- [ ] **0.4** **`Subtype.measurableSingletonClass` の存在確認** (inventory §F 主要前提条件
  ボックスの未確認項目):
  ```bash
  rg "instance.*MeasurableSingletonClass.*Subtype|measurableSingletonClass.*Subtype" \
    .lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/
  ```
  もし不在なら、`[MeasurableSingletonClass α']` の自前付与 ~10 行を Phase 3 冒頭に追加予定として
  メモ (撤退ライン §G-2 (a) の予防的代替: §F-3 (ii) 型不変経路への退避は本 plan 既定方針)。
- [ ] **0.5** `induction hn : Fintype.card α using Nat.strong_induction_on generalizing α P l`
  の **`generalizing α` で `[Fintype α]` etc. type-class が同時 generalize されるか** を 1 行 probe:
  ```lean
  example {α : Type*} [Fintype α] (P : ℕ → Prop) : P (Fintype.card α) := by
    induction hn : Fintype.card α using Nat.strong_induction_on generalizing α
    sorry
  ```
  失敗するなら **§F-4 (a) `Fintype.card α` 上の strong induction** を諦め、§F-4 (b) `s.card` 上に
  pivot する必要あり (= IH を `huffmanLengthAux s` 上で書く、inventory §F-3 (ii) と整合)。
- [ ] **0.6** `loogle "Subtype, Nonempty, ne"` で `Subtype.nonempty_of_exists` 系の signature
  確認 (`α'` の `[Nonempty α']` 取り出し、inventory §「主要前提条件ボックス」).

Phase 0 で 0.4 / 0.5 が negative ヒットした場合は **判断ログに #1 を起こし**、抽象水準を
再評価 (C-1 の暫定確定を覆す可能性あり)。

## Phase 1 — skeleton (`HuffmanOptimality.lean` 新規ファイル、全 sorry) 📋

新規ファイル `Common2026/Shannon/HuffmanOptimality.lean` を Write、全 sorry で LSP silent
(sorry warning のみ) を確認。inventory §「着手 skeleton」(~50 行) をベースに、後続 Phase で
追加予定の helper signature 群も sorry で立ち上げる。

- [ ] **1.1** ファイル冒頭 (module doc + import + open namespace + variable 宣言).
- [ ] **1.2** `exists_sibling_min_pair` の宣言 (sorry).
- [ ] **1.3** `huffmanLength_optimal` (主定理、sorry).
- [ ] **1.4** Phase 2 内部 helper (sibling 候補): `exists_deepest_leaf` (sorry),
  `huffmanLength_eq_of_min_prob_pair` (sorry).
- [ ] **1.5** Phase 3 内部 helper (lift bridges): `mergedMeasure` (def, sorry placeholder),
  `mergedMeasure_real` (sorry), `huffmanLength_bridge_L` (sorry),
  `expectedLength_bridge_R` (sorry).
- [ ] **1.6** `Common2026.lean` に `import Common2026.Shannon.HuffmanOptimality` 追記、
  `lake env lean Common2026.lean` silent を確認.

skeleton 全体は ~80 行見込み (publish 面 2 件 + helper 6 件)。

## Phase 2 — `exists_sibling_min_pair` (Cover-Thomas Lemma 5.8.1) 📋

inventory §B + §C の API で Cover-Thomas Lemma 5.8.1 を formalization。

- [ ] **2.1** 内部 helper `exists_deepest_leaf (P : Measure α) (h_card : 1 ≤ Fintype.card α)`:
  `∃ a, ∀ c, huffmanLength P c ≤ huffmanLength P a`. `Finset.exists_max_image
  (Finset.univ : Finset α) (huffmanLength P)` を unfold した形 (~15 行、inventory §「自作要 §1」).
- [ ] **2.2** 内部 helper `huffmanLength_const_on_initGroup`:
  T1-A 既存 `huffmanLengthAux_const_on_group` を `initMultiset P` で specialize し、「初期 group
  (singleton `{a}`) が後の merge step で同一 group に統合される ⇒ `huffmanLength P a =
  huffmanLength P b`」 を取り出す bridge (~20 行).
- [ ] **2.3** Cover-Thomas Lemma 5.8.1 (i) (最深 leaf と最小確率は swap 可) を `private theorem`
  で抽出: `Equiv.swap a b` で `l` を書き換えても `expectedLength` は不変 + `huffmanLength` 側の
  最深 leaf 性質も保持 (~50 行、inventory §C `Equiv.swap_apply_*` + §D `Finset.sum_pair`).
- [ ] **2.4** Cover-Thomas Lemma 5.8.1 (ii) (最深 leaf の兄弟も最深) を `private theorem` で
  抽出: T1-A 既存 `huffmanStep_spec` で最後の merge step に現れる 2 element の `huffmanLength`
  値が等しいことを取り出す (~30 行).
- [ ] **2.5** `exists_sibling_min_pair` 本体: 2.1-2.4 を合成. `huffmanStep (initMultiset P) ...`
  の最後の merge step で取り出される `(x1, x2)` ペアが「等深 + 最小確率」を満たすことを確認
  (~35 行).
- [ ] **2.6** `lake env lean Common2026/Shannon/HuffmanOptimality.lean` silent (Phase 3 部分の
  sorry は許容、Phase 2 部分のみ 0 sorry).

**規模**: ~150 行 (helper ~85 行 + 本体 ~65 行).

**撤退ライン §G-3 ガード** (inventory §G-3): Phase 2.3 / 2.4 で 5 ターン進まない場合、
**sibling property を `axiom` として仮定する弱版** に切り替え、本 Phase scope-out。後続 seed
`T1-A''` に分離。本 plan は弱形 wrap-up。

**注意点 (inventory §「自作要」優先度 1 から)**: 「2 つの最深兄弟」を `huffmanLength P` の値
だけから取り出すには、`initMultiset P` の最深 group `p ∈ initMultiset P` が `p.1.card ≥ 2` を
満たすことを示す必要 (= 最深 group は必ず最後の merge step で生まれた `merged group`)。
これは Huffman merge の構造的性質で、`huffmanLengthAux_eq_step` の逆向きの不変量 lemma
(~50 行) を 2.4 内部で起こす。

## Phase 3 — Subtype `α'` lift bridges (merged measure + Bridge L + Bridge R) 📋

C-1 のハイブリッド設計 (§F-2 (i) Subtype + §F-3 (ii) 型不変) の core 実装。`α' := { x : α //
x ≠ b }` 上で `huffmanLength` を呼ぶ際の cross-type bridge を建てる。**本 plan で最大の Phase**。

### Phase 3.1: `α'` 型と type-class 継承の verification (~30 行)

- [ ] **3.1.1** `private def α' (b : α) : Type* := { x : α // x ≠ b }` (一行抽象、以下も同じ).
- [ ] **3.1.2** Phase 0.4 の結果に従い、`[Fintype α']` / `[DecidableEq α']` /
  `[MeasurableSpace α']` / `[MeasurableSingletonClass α']` の継承を確認:
  - Mathlib auto-derive で済むなら 0 行追加.
  - `MeasurableSingletonClass α'` が auto でない場合は自前 instance 付与 ~10 行 (`MeasurableSet
    {⟨x, hx⟩}` を `MeasurableSet {x}` から `Subtype.val` の measurability で取る).
- [ ] **3.1.3** `[Nonempty α']` を `h_card : 2 ≤ Fintype.card α` から手作業で取り出す helper
  `α'_nonempty (h_card : 2 ≤ Fintype.card α) (b : α) : Nonempty { x : α // x ≠ b }` (~10 行).

### Phase 3.2: `mergedMeasure P a b : Measure α'` の構成 + `IsProbabilityMeasure` (~80 行)

- [ ] **3.2.1** C-3 の point-mass 直接構成 (`Measure.dirac` の finite sum 形). 各 singleton
  `{⟨x, hx⟩}` への measure 値は `if x = a then P.real {a} + P.real {b} else P.real {x}`.
- [ ] **3.2.2** `mergedMeasure_real` (~20 行): 各 singleton への point-mass 値の `Measure.real`
  ≪→ ℝ 変換.
- [ ] **3.2.3** `IsProbabilityMeasure (mergedMeasure P a b hab)` instance (~30 行):
  `∑ x : α', mergedMeasure.real {x} = ∑ a : α, P.real {a} = 1` を `Finset.sum_pair` +
  `Finset.mul_prod_erase` で示す.
- [ ] **3.2.4** `mergedMeasure_pos`: `∀ x : α', 0 < (mergedMeasure P a b hab).real {x}`
  (~20 行、`hP : ∀ a, 0 < P.real {a}` の lift).

### Phase 3.3: Bridge L — Huffman 側 `huffmanLength P` と `huffmanLength (mergedMeasure ...)` の等式 (~60 行)

```lean
-- sketch
lemma huffmanLength_bridge_L
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) (a b : α) (hab : a ≠ b)
    (h_sibling : ...) :
    expectedLength P (huffmanLength P)
      = expectedLength (mergedMeasure P a b hab) (huffmanLength (mergedMeasure P a b hab))
        + (P.real {a} + P.real {b})
```

- [ ] **3.3.1** sibling property の取得 (Phase 2 `exists_sibling_min_pair`) で
  `huffmanLength P a = huffmanLength P b = depth` を確定.
- [ ] **3.3.2** **T1-A `huffmanLengthAux_step_merged` の直接 reuse**: `initMultiset P` の最後
  merge step (`huffmanStep` 1 回適用) で `a, b` が merged group `{a, b}` に統合されることを
  示し、`huffmanLengthAux (initMultiset P) a = huffmanLengthAux (step result) a + 1` を
  取り出す (この箇所が「既存 step lemma の verbatim 再利用」、+30 行節約).
- [ ] **3.3.3** `huffmanLengthAux_step_other` の `α'` 側 instantiation で `b ≠ x ⇒
  huffmanLengthAux (initMultiset P) x = huffmanLengthAux (mergedMeasure 経由の initMultiset
  P' に対応する Multiset) x` を取り出す (+30 行節約).
- [ ] **3.3.4** `expectedLength` 等式へ昇格: `Finset.sum_pair` で `(a, b)` の項を抜き出し、
  `Finset.sum_attach` + `Finset.sum_subtype_of_mem` で `α'` 上の sum と bridge.

### Phase 3.4: Bridge R — 任意 `l` 側の不等式 (鍵 lemma、~80 行)

```lean
-- sketch
lemma expectedLength_bridge_R
    (P : Measure α) (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (a b : α) (hab : a ≠ b) (h_swap_normalized : l a = l b ∧ ∀ c, l c ≤ l a) :
    expectedLength P l
      ≥ expectedLength (mergedMeasure P a b hab) (liftL l a b) + (P.real {a} + P.real {b})
```

ここで `liftL l a b : α' → ℕ` は `if x.val = a then l a - 1 else l x.val` (+1 ペナルティ吸収).

- [ ] **3.4.1** `liftL` の定義 + `liftL_pos` (~20 行). `l a ≥ 1` から `l a - 1 ≥ 0`.
- [ ] **3.4.2** Kraft 不等式の lift: `∑ x : α', (2 : ℝ) ^ (-(liftL l a b x : ℤ)) ≤ 1`. `+1`
  ペナルティ吸収 (`2 ^ (-(d : ℤ)) = 2 ^ (-((d+1) : ℤ)) + 2 ^ (-((d+1) : ℤ))`) — inventory §G
  既出 identity を Phase 3 helper として独立補題化 ~5 行.
- [ ] **3.4.3** `expectedLength` の不等式: `expectedLength P l = expectedLength P' (liftL l a b)
  + (P.real {a} + P.real {b}) - (gap項)` の **`gap項 ≥ 0`** を示す. これは sibling property
  正規化済 `l a = l b` を使う鍵 step.

### Phase 3.5: verify (~5 行)

- [ ] **3.5.1** `lake env lean Common2026/Shannon/HuffmanOptimality.lean` を Phase 2 + 3 部分
  で silent 確認 (Phase 4 主定理 sorry は許容).

**規模**: ~250 行 (3.1: 30 + 3.2: 80 + 3.3: 60 + 3.4: 80 + 3.5: verify).

**撤退ライン §G-2 ガード** (inventory §G-2): Phase 3.1.2 で `MeasurableSingletonClass α'`
auto-derive が確認できず自前付与 ~50 行が必要になる場合、判断ログに #2 を起こし
**§F-3 (ii) 型不変経路への完全 pivot** を検討 (Subtype `α'` を作らず、`Multiset (Finset α × ℝ)`
上の IH のみで主定理を回す)。

## Phase 4 — 主定理 `huffmanLength_optimal` (`n → n-1` induction 合成) 📋

`Fintype.card α` 上の `Nat.strong_induction_on` で n→n-1 induction を回す。Phase 0.5 の
generalizing 確認で `Nat.strong_induction_on` が動かない場合は `s.card` 上に切り替え (C-1
§F-4 (a) → (b) pivot 想定済)。

- [ ] **4.1** induction 設定:
  ```lean
  induction hn : Fintype.card α using Nat.strong_induction_on generalizing α P l
    with
    | _ n IH => ...
  ```
  (Phase 0.5 の結果次第で具体 tactic は微調整).
- [ ] **4.2** base case `n ≤ 1`: `huffmanLength = 0` (T1-A 既存 `huffmanLengthAux_eq_zero`),
  `expectedLength P (huffmanLength P) = 0 ≤ expectedLength P l` (`hl_pos` から).
- [ ] **4.3** step case `n ≥ 2`:
  - `exists_sibling_min_pair P hP h_card` で `(a, b)` 取得.
  - sibling property + Cover-Thomas Lemma 5.8.1 (i) で任意 `l` を `l_swap` に正規化
    (`Equiv.swap` で `l_swap a = l_swap b` 達成、Phase 2.3 lemma の reuse).
  - Bridge L (Phase 3.3) で Huffman 側の `expectedLength` を `α'` 側 + `(P.real {a} + P.real {b})` に分解.
  - Bridge R (Phase 3.4) で任意 `l_swap` 側の `expectedLength` を `α'` 側 + `(P.real {a} +
    P.real {b})` に分解.
  - IH 適用: `expectedLength P' (huffmanLength P') ≤ expectedLength P' (liftL l_swap a b)`.
    `Fintype.card α' = Fintype.card α - 1 < n` で IH 適用可 (`Fintype.subtype_card` で取得).
  - 上記 3 段を合成し、`expectedLength P l_swap = expectedLength P l` (swap 不変、Phase 2.3
    lemma) で `l_swap` から `l` に戻す.
- [ ] **4.4** `lake env lean` silent.

**規模**: ~100 行 (base case ~15 行 + step case 合成 ~85 行).

## Phase 5 — verify + regression check 📋

- [ ] **5.1** `lake env lean Common2026/Shannon/HuffmanOptimality.lean` を 0 sorry / 0 error /
  最小 warning で確認.
- [ ] **5.2** regression check (既存 0-sorry ファイル):
  - `Common2026/Shannon/Huffman.lean` (T1-A 完了形、953 行 / 0 sorry を維持).
  - `Common2026/Shannon/ShannonCode.lean`.
  - `Common2026/Shannon/ShannonCodeKraftReverse.lean`.
  - いずれも `lake env lean` silent.
- [ ] **5.3** `Common2026.lean` の import 追記済を確認、`lake build Common2026` で全 silent.
- [ ] **5.4** `textbook-roadmap.md` の Ch.5 行を 🟢 へ昇格 (T1-A' 完了で Ch.5 完成判定).

**規模**: 0 行 (verify のみ).

## 判定条件 (Definition of Done)

`lake env lean Common2026/Shannon/HuffmanOptimality.lean` が **0 sorry / 0 error / 最小 warning**
で pass、かつ以下が全て満たされる:

- [ ] `exists_sibling_min_pair` (Cover-Thomas Lemma 5.8.1) が publish.
- [ ] `huffmanLength_optimal` (Cover-Thomas Theorem 5.8.1、任意 Kraft-feasible `l` 比較形) が
  publish.
- [ ] T1-A 既存 `Common2026/Shannon/Huffman.lean` は **不変** (953 行 / 0 sorry).
- [ ] 既存 `ShannonCode.lean` / `ShannonCodeKraftReverse.lean` に regression なし.
- [ ] `Common2026.lean` に `import Common2026.Shannon.HuffmanOptimality` 追記済.
- [ ] `textbook-roadmap.md` Ch.5 行 🟢 昇格.

## 撤退ライン

inventory §G の §G-1〜§G-3 を踏襲。発動条件 / 対応 / 判断は inventory verbatim で参照、
本 plan では発動時の **追加対応** のみ記載。

### §G-1. 規模が ~500 行を超え ~700+ に達する

- inventory §G-1 (a) 弱形 publish (`huffmanLength_le_shannonLength` のみ): **発動 NG**
  (T1-A 当初の弱形に戻ると T1-A → T1-A' 分離意義が失われる).
- 本 plan **追加対応**: `α'` 型不変経路 (§F-3 (ii)) に完全 pivot、Subtype 路線を捨てて
  `Multiset (Finset α × ℝ)` 上の IH のみで主定理を回す。inventory §F-3 末尾「推奨 (ii)」の
  ~500 行収束ライン。

### §G-2. Subtype `α'` の `MeasurableSingletonClass` auto-derive が確認できない

- inventory §G-2 (a) 型不変経路へ pivot: 本 plan §C-1 のハイブリッド設計のうち §F-2 (i)
  Subtype 採用を撤回、§F-3 (ii) のみで完結。
- 本 plan **追加対応**: 判断ログに #2 を起こし、Phase 3 を全面書き直し。Phase 2 / Phase 4 は
  影響軽微 (sibling property + induction frame は不変、bridge の中身だけ書き直し).

### §G-3. Phase 2 sibling property の swap argument が 5 ターン進まない

- inventory §G-3 対応: 本 plan scope-out、sibling property を `axiom` 仮定の弱版へ後退、
  別 seed `T1-A''` (更に分離) に切り出し。
- 本 plan **追加対応**: 本 plan は弱形 wrap-up としてその時点で 0 sorry close。主定理
  `huffmanLength_optimal` は `axiom exists_sibling_min_pair` の仮定下で publish 可能、
  この弱形でも roadmap Ch.5 行は 🟡 のまま (🟢 昇格は T1-A'' 完遂で).

## 規模見積もり / 想定ターン数

- 行数: **~500 行** (binary 限定 + ハイブリッド設計 + T1-A 既存 step lemma 再利用で 500 行
  収束、inventory §H 推奨設計と整合).
- ターン数: **~12-18 ターン** (Phase 0 ×1, Phase 1 ×1, Phase 2 ×3-4, Phase 3 ×5-7, Phase 4
  ×2-3, Phase 5 ×1).
- 想定実装時間: **2-3 セッション** (Phase 2 で 1 セッション、Phase 3 で 1-2 セッション、
  Phase 4 + 5 を最終セッションで合成).

## 後続 seed への影響

T1-A' 完了で `textbook-roadmap.md` Ch.5 行 🟢 昇格 (data compression 完成扱い)。直接的な後続:

- **T3-E Separation Theorem** (Ch.5 + Ch.7 統合): Huffman の最適性を引用できる状態に。
- **T4-A LZ78** (universal coding, Ch.13): 「prefix code 最適性 (Huffman) vs universal 漸近
  最適性 (LZ78)」の対比を教科書原稿で書ける.
- **教科書原稿 Ch.5**: Shannon code + Kraft + Huffman 三柱 + Huffman optimality を 0-sorry
  リンクで書ける状態。

T1-A'' (D-ary 拡張 / sibling property 別経路) は本 plan 完遂後に必要なら起こす。default は
binary 完遂で Ch.5 終了。

## 次セッション最初の一手

**Phase 1 skeleton を実装者に引き渡し**:

> Phase 1 skeleton `Common2026/Shannon/HuffmanOptimality.lean` を新規 Write。
> import + namespace + variable + `exists_sibling_min_pair` / `huffmanLength_optimal`
> 主役 2 件 + Phase 2/3 helper 6 件を **全て `:= by sorry`** で立ち上げ、LSP silent
> (sorry warning のみ) を確認。`Common2026.lean` に `import Common2026.Shannon.HuffmanOptimality`
> を `import Common2026.Shannon.Huffman` 直後に追加し、`lake env lean Common2026.lean` silent
> 確認まで。Phase 0 (在庫再確認 + 型クラス継承確認) は Phase 1 skeleton と並行 1 ターンで処理可。

## 参考

- Parent roadmap: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A'」
- Inventory: [`huffman-optimality-mathlib-inventory.md`](./huffman-optimality-mathlib-inventory.md)
- 先行 plan (T1-A 完了 archive): [`huffman-moonshot-plan.md`](./huffman-moonshot-plan.md)
- 先行実装 (T1-A): `Common2026/Shannon/Huffman.lean` (953 行 / 0 sorry).
- 既存 `expectedLength`: `Common2026/Shannon/ShannonCode.lean:55`.
- 既存 `IsPrefixFree` / `exists_prefix_code_of_kraft`:
  `Common2026/Shannon/ShannonCodeKraftReverse.lean:47, :482`.
- T1-A 既存 API (`Common2026/Shannon/Huffman.lean`):
  - `huffmanLength`: `:337`
  - `huffmanLengthAux`: `:278`
  - `huffmanLengthAux_eq_step`: `:305`
  - `huffmanLengthAux_step_merged`: `:614`
  - `huffmanLengthAux_step_other`: `:625`
  - `huffmanLengthAux_const_on_group`: `:467`
  - `huffmanStep`: `:67`
  - `huffmanStep_spec`: `:231`
  - `huffmanLength_pos`: `:451`
  - `huffmanLength_kraft_le_one`: `:923`
- Mathlib path (inventory verbatim):
  - `Equiv.swap`: `Mathlib/Logic/Equiv/Basic.lean:634`
  - `Function.update`: `Mathlib/Logic/Function/Basic.lean:628`
  - `Finset.exists_max_image`: `Mathlib/Data/Finset/Max.lean:525`
  - `Finset.mul_prod_erase`: `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:741`
  - `Finset.sum_pair`: `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:86`
  - `Finset.sum_attach`: `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:100`
  - `Nat.strong_induction_on`: `Mathlib/Data/Nat/Init.lean:281`
  - `Finset.image_erase`: `Mathlib/Data/Finset/Image.lean:444`
  - `Finset.one_lt_card`: `Mathlib/Data/Finset/Card.lean:721`
- Cover & Thomas *Elements of Information Theory* 2nd ed.,
  - **Lemma 5.8.1** (sibling property, swap argument)
  - **Theorem 5.8.1** (Huffman optimality, n → n-1 induction)
- フォーマット参考: [`huffman-moonshot-plan.md`](./huffman-moonshot-plan.md),
  [`general-dmc-plan.md`](./general-dmc-plan.md).
- 雛形: [`moonshot-plan-template.md`](../moonshot-plan-template.md).

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

0. **2026-05-19 起草 — 規模超過/撤退発動の判断枠予約**: 本 plan 起草時点で、inventory §G-1〜§G-3
   のいずれかが将来発動する場合の判断枠を予約する (C-4 で plan 化済)。**1 セッション内での
   発動は禁止**、2 セッション目以降で実装規模 / 行数 / ターン数の見通しが本 plan §「規模見積もり」
   を大きく逸脱した場合のみ append 検討。T1-A 判断ログ #2-#4 の「単一セッション 0 sorry を
   狙わず 2-3 セッションに分割」の教訓を踏襲。

1. **2026-05-19 起草 — 設計判断の確定 (C-1〜C-4)**: inventory (`huffman-optimality-mathlib-inventory.md`)
   §F-2 / §F-3 / §F-4 + §H 推奨設計を受けて C-1〜C-4 を確定。
   - **C-1 (抽象水準ハイブリッド)**: §F-2 (i) Subtype + §F-3 (ii) 型不変 + §F-4 (b)
     `Nat.strong_induction_on` の 3 軸組み合わせ。Quotient 経路 (§F-2 (ii)) は撤退ラインで言及
     のみ、採用しない。
   - **C-2 (sibling property 統合形)**: inventory §F-1 候補 (a) 採用、内部分解は private theorem.
   - **C-3 (merged measure point-mass 直接構成)**: `Measure.map` / `Measure.restrict` 経由しない、
     point-mass `Measure.dirac` finite sum 形で ~30 行、bridge 補題 1 件に閉じる.
   - **C-4 (撤退ライン発動の事前枠)**: 判断ログにエントリ #0 (上記) を予約、2 セッション目以降の
     規模超過判定で初めて検討.
   - **規模見積もり ~500 行**: T1-A 既存 step lemma (`huffmanLengthAux_step_merged` /
     `_step_other` / `_const_on_group` etc.) の verbatim 再利用で inventory §「自作要」の
     ~725 行から ~225 行節約。inventory §H 1 行サマリの「~500 行で完成」と整合.

2. **2026-05-19 — Phase 2 sibling lemma signature 縮退 (案 B pivot)**:
   `huffmanStep_initMultiset_sibling` で 3/4 条件 (`a ≠ b`、`huffmanLength P a = huffmanLength P b`、
   最小確率ペア) は 0 sorry 確立済だが、4 条件目「`∀ c, huffmanLength P c ≤ huffmanLength P a`」
   (最深性) のみ 5 ターン進まず撤退ライン §G-3 暫定発動。`huffmanLengthAux_max_at_first_pair`
   invariant 単独で ~80-120 行 (悲観 ~200 行) と判定、inventory §「自作要」§1 の ~50 行見積を超過。
   pivot: **`exists_sibling_min_pair` から最深性条項を削除**、Phase 4 step case 側で
   `Finset.exists_max_image (huffmanLength P)` を独立に呼んで `l` 側 swap argument 経路で補完。
   Cover-Thomas Lemma 5.8.1 (i) standard 証明と整合、撤退ライン §G-3 axiom 後退は回避。

3. **2026-05-19 — Phase 3.3 signature pivot + Phase 3.4 `0 < l'` 削除**: Phase 3.3 実装で
   `huffmanLength (mergedMeasure P a b hab)` (α' 型) と T1-A `huffmanLengthAux_step_*` (α 型)
   の型不一致が露顕、structural correspondence 補題 ~80-120 行 (proof-pivot-advisor 評価)
   が必要と判明 → bridge L の signature を sibling-driven 分解形に再 shape (case ii)、
   `huffmanLength P'` との同一視を Phase 4 側 `huffmanLength_mergedMeasure_eq` に後送。
   Phase 3.4 で `0 < l' x` clause が `card α = 2 ∧ l ≡ 1` で反例があり削除、`card α = 2`
   を Phase 4 base case で inline 処理 (case A)。`mergedMeasure` 定義 pivot (Measure.map 経由化、
   §C-3 撤回) は機会費用大のため見送り。

4. **2026-05-19 — Phase 3.1+3.2 + Phase 4 base case + step case 合成 完了**: `mergedMeasure`
   (point-mass 直接構成) + `mergedMeasure_real` + Bridge L (sibling-driven 形) + Bridge R
   (`(h_la_ge_2 : 2 ≤ l a)` 追加 + positivity 結論復活、Phase 4 専用補強) + Phase 4 base case
   (`card ≤ 2` 拡張) + Phase 4 step case 合成 まですべて 0 sorry。`huffmanLength_optimal_aux`
   の証明骨格 (`linarith` + IH + Bridge L/R 連結) 完成。残 2 sorry: `exists_swap_normalized`
   + `huffmanLength_mergedMeasure_eq`。

5. **2026-05-19 — `swap_step_le` helper publish (~96 行 0 sorry)**: `Equiv.swap a m` 経由の
   1 step 不変量 (positivity, Kraft 不変, expected length 非増加, swap 後値特定) をパック。
   `exists_swap_normalized` の中核ビルディングブロック。

6. **2026-05-19 — `exists_swap_normalized` ブロッカー判明 + signature バグ発見 (Sorry #2)**:
   実装中に判明:
   - **Sorry #1 (`exists_swap_normalized`)**: 2-step swap 単独では `l_norm a = l_norm b`
     一般に保証できない (実例 `l = (3, 1, 2)`)。Cover-Thomas 標準証明では **Kraft = 1 (full
     binary tree)** 仮定が必要 → 最深 leaf が pair で存在。arbitrary `l` (Kraft `≤ 1`) を
     normalize するには先に `l` を Kraft = 1 化する shortening 補題が要 (~50-100 行追加)。
   - **Sorry #2 (`huffmanLength_mergedMeasure_eq`) の signature バグ**: `h_sibling` 単独では
     反例あり (`P{α₁} = P{α₂} = 0.1, P{α₃} = P{α₄} = 0.4` で α₃, α₄ が同 huffmanLength
     でも min-prob pair ではない)。**`h_a_min` / `h_b_min` 強化必須**。

7. **2026-05-19 — 案 Y (weak form publish) 採用、T1-A' 結了**: 案 X (Sorry #1 + Sorry #2
   を ~220-360 行 で 0 sorry 化) の context cost vs 案 Y (~50 行 で確実 0 sorry) を比較し、
   **`huffmanLength_optimal_with_hypotheses` weak form** を T1-A' の publish 形式に確定。
   - `SwapNormalizationHypothesis` + `HuffmanMergedIdentificationHypothesis` を universe-
     polymorphic `abbrev Prop` で hypothesis pass-through 化。
   - 主定理 `huffmanLength_optimal_with_hypotheses` は 2 hypothesis を引数で受け取り、
     `expectedLength P (huffmanLength P) ≤ expectedLength P l` を証明 (0 sorry、0 error)。
   - **副産物**: `Huffman.lean` に `huffmanLength_kraft_eq_one` (Kraft `= 1` 等号版) を
     publish (~14 行、`kraftPerGroup_eq_one` + `kraftPerGroup_initMultiset_eq_kraft` 経由)。
     既存 `huffmanLength_kraft_le_one` は `= 1` 版を `le_of_eq` で経由する形にリファクタ。
   - **後継 seed T1-A''**: 2 hypothesis を discharge し強形 `huffmanLength_optimal`
     (hypothesis 引数なし) を publish。スコープ: swap normalization (Kraft = 1 shortening
     込み、~150-200 行) + identification (`huffmanLengthAux` α/α' structural correspondence、
     ~150-200 行)。`docs/shannon/huffman-optimality-t1apprime-plan.md` 等で別 plan 化。
   - **規模実績**: `HuffmanOptimality.lean` 1054 行 + `Huffman.lean` +14 行 (T1-A' 部分)。
     plan 起草時 ~500 行見積から大幅超過、主因は (a) Phase 3.3 signature pivot で
     `huffmanLength_mergedMeasure_eq` を Phase 4 helper に縮退 (Phase 3 シンプル化 ↔
     Phase 4 hypothesis 化)、(b) `swap_step_le` ~96 行 helper を T1-A'' 向け中核として残置、
     (c) Bridge R で positivity 復活 / Kraft 経由 rewrite が当初見積を超過。

# Han 不等式ムーンショット (Phase A/B/C) Lean 形式化 — ボトルネック分析

将来「Pi 値の `MeasurableEquiv` reshape boilerplate を生成するエージェント」「`Fin n` の prefix / 補集合 / sum-product 分解の index 同型を自動構築するツール」「`set_option in` / docstring / private 修飾子の順序を静的に検査する linter」を作るためのベースライン記録。Han 不等式 (補集合形) を Mathlib + 既存 `Common2026/Shannon` API の上に **6 セッション**で完走した記録。

**定量データ**: [docs/metrics/han-moonshot.metrics.md](../metrics/han-moonshot.metrics.md)

## 0. 対象問題と成果物

最終定理:

```lean
theorem han_inequality
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    ((n : ℝ) - 1) * jointEntropy μ Xs
      ≤ ∑ i : Fin n, jointEntropyExcept μ Xs i
```

`jointEntropy μ Xs := entropy μ (fun ω i => Xs i ω)` (`entropy` の `Fin n → α`-値ラッパ)。当初想定していた `hn : 1 ≤ n` 仮定は **n = 0, 1 退化ケースが同じ証明で通る** ため不要だった (n = 0 では LHS = (-1)·0 = 0、RHS = 空和 = 0)。

成果物:

- `Common2026/Shannon/Entropy.lean` — Phase A の 4 主定理を実装、**250 行** (skeleton 98 行 → 充填 +152 行)、0 errors / 0 sorry
  - `entropy_pair_eq_entropy_add_condEntropy` (chain rule、~70 行)
  - `condEntropy_tower` (補助補題、~40 行)
  - `condMutualInfo_eq_condEntropy_sub_condEntropy` (中間補題、~30 行)
  - `condEntropy_le_condEntropy_of_pair` (条件付けで減る、3 行)
  - 副産物: `mutualInfo_ne_top` / `condMutualInfo_ne_top` (有限性、`MutualInfo.lean` / `CondMutualInfo.lean` に追加)
- `Common2026/Shannon/Han.lean` — Phase B + C を実装、**382 行**、0 errors / 0 sorry
  - `jointEntropy` / `jointEntropyExcept` (定義、~10 行)
  - `entropy_measurableEquiv_comp` (private helper、`MeasurableEquiv` で push-forward 不変、~30 行)
  - `jointEntropy_chain_rule` (Phase B、`Fin n` induction、~75 行)
  - `exceptIdxEquiv` / `fullIdxEquiv` (Phase C、index 同型 2 本、~60 行)
  - `exceptSplitMEquiv` / `piExceptMEquiv` / `fullSplitMEquiv` (Pi 値 `MeasurableEquiv` 3 本、~35 行)
  - `han_single_bound` (各 i 個別不等式、~85 行)
  - `han_inequality` (主定理、~25 行)
- `docs/han/han-moonshot-plan.md` — 4 段プラン (Phase 0/A/B/C)
- `docs/han/han-mathlib-inventory.md` — Phase 0 在庫調査

`lake env lean Common2026/Shannon/Han.lean` 通過 (silent)。

## 1. 問題のキャラクター

「**新規測度論プリミティブ不要、ただし Pi 値の `MeasurableEquiv` plumbing が支配項**」型。Phase 0 在庫調査で「Mathlib に Han / Shearer 不在」「`Fin n → α` の instance チェイン (`Pi.fintype`, `MeasurableSpace.pi`, `Pi.instMeasurableSingletonClass`) は自動発火確認」が事前確定しており、**新規 Mathlib 探索ターンを消費せずに既存 API の n 変数化だけにフォーカス**できた点で過去のムーンショットと違う。

支配項は **Phase C の Pi 値 reshape**: `Fin n → α` を `α × ((Fin i.val → α) × ({j // i < j} → α))` に分解する `MeasurableEquiv` の自作 plumbing が ~95 行で本ファイル 382 行のうち約 25%。

過去のフェーズとの規模感比較:

| Phase | 主要ファイル | 行数 (実装分) | 性格 |
|---|---|---|---|
| Phase 4-α (DPI) | `Common2026/Shannon/DPI.lean` | 168 行 | klDiv の DPI 接続 |
| Phase 4-β (bridge) | `Common2026/Shannon/Bridge.lean` | 588 行 | KL ↔ entropy − condEntropy 同値 |
| Phase 4-γ (Shannon converse) | `Common2026/Shannon/Converse.lean` | 124 行 | plumbing 層の組み合わせ |
| Phase 4-δ-(b) (Markov encoder) | `Common2026/Shannon/CondMutualInfo.lean` | 353 行 | condMI 定義 + chain rule 自作 plumbing |
| **Han Phase A (本回)** | **`Common2026/Shannon/Entropy.lean`** | **+152 行** | 2 変数 chain rule + 「条件付けで減る」 |
| **Han Phase B+C (本回)** | **`Common2026/Shannon/Han.lean`** | **382 行** | n 変数 chain rule + Pi 値 reshape plumbing + Han |

## 2. 数学的方針

### Phase A: 2 変数 entropy 補題 (既存 `mutualInfo` 経由)

中間補題 `condMutualInfo_eq_condEntropy_sub_condEntropy` (`I(X; Z | Y) = H(X|Y) - H(X|Y,Z)`) を起点に、`condEntropy_le_condEntropy_of_pair` (条件付けで減る) は `condMutualInfo_nonneg` から直接 3 行で出る。

中間補題自体は教科書的には `condMutualInfo` を fiber 上で `mutualInfo_eq_entropy_sub_condEntropy` (Bridge) に展開する経路を想定したが、**fiber 展開ルートを却下** (理由は §4.2)。代わりに:

```
mutualInfo_chain_rule μ Z X Y                          -- compProd 形 chain rule (既存)
  ↓ mutualInfo_comm × 2 + condMutualInfo_comm × 1     -- Xs を第1引数に統一
mI(X; (Y, Z)) = mI(X; Y) + cMI(X; Z | Y)               -- ENNReal 形
  ↓ ENNReal.toReal_add (有限性必要)
.toReal: mI(X; (Y,Z)).toReal = mI(X; Y).toReal + cMI(X; Z|Y).toReal
  ↓ mutualInfo_eq_entropy_sub_condEntropy × 2 (Bridge を 2 回)
H(X) - H(X|Y,Z) = (H(X) - H(X|Y)) + cMI(X; Z|Y).toReal
  ↓ linarith (entropy μ Xs を相殺)
cMI(X; Z|Y).toReal = H(X|Y) - H(X|Y,Z)
```

### Phase B: n 変数 chain rule (`Fin n` induction)

step (`n + 1`) で `Fin (n+1) → α` を `α × (Fin n → α)` (= `(Xs (last n), prefix)`) に `MeasurableEquiv.piFinSuccAbove` で reshape し、Phase A の `entropy_pair_eq_entropy_add_condEntropy` を 1 段適用 → IH で n-prefix を展開 → `Fin.sum_univ_castSucc` で和を整形。

base (`n = 0`) は `entropy μ (fun ω (i : Fin 0) => Xs i ω) = 0` を `Pi.uniqueOfIsEmpty` + `Subsingleton.elim` で trivial 化。

### Phase C: Han 本体 (組み合わせのみ)

各 `i : Fin n` に対し:

```
H(Xs) - H(Xs except i) ≤ H(Xs i | prefix)
       (Phase A chain rule + 「条件付けで減る」を 1 段ずつ)
```

を `han_single_bound` として確立し、`Finset.sum_le_sum` で和を取り、Phase B の `jointEntropy_chain_rule` で RHS を `H(Xs)` に縮約。最後に `Finset.sum_sub_distrib` + `linarith` で完了。

ここで「prefix」とは `fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω` (= `Xs` の最初 `i` 個)、「except」とは `fun ω (j : {j // j ≠ i}) => Xs j.val ω` (= `Xs` から `i` を除いた残り)。

`han_single_bound` の山は:

1. `entropy μ (fun ω => (prefSuff ω, Xs i ω)) = jointEntropy μ Xs`
   ((`prefix × suffix`) × `α` ≃ᵐ `Fin n → α`)
2. `entropy μ prefSuff = jointEntropyExcept μ Xs i`
   (`prefix × suffix` ≃ᵐ `{j // j ≠ i} → α`)

の 2 本の `MeasurableEquiv` 等価性。これに `~95 行 / Phase C 全体の約 35%` を消費。

## 3. Mathlib 補題探索の実録

Phase 0 在庫調査 (`docs/han/han-mathlib-inventory.md`) で chain rule / condDistrib 周辺は事前にマップ済。実装中に loogle を **Phase A だけで 44 回 / Phase B 13 回 / Phase C 7 回** 打って追加検索した (合計 64 回、`Common2026/Shannon/` への loogle 投入歴で最多級)。

**見つかった主要補題** (実際に使ったもの):

| 用途 | 場所 | 探索 |
|---|---|---|
| Phase A chain rule の主役 | `Mathlib/Probability/Kernel/CondDistrib.lean` `compProd_map_condDistrib` | inventory |
| `Real.negMulLog_mul`: `negMulLog (a*b) = a · negMulLog b + b · negMulLog a` 風 | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean` | loogle `Real.negMulLog_mul` |
| `MeasureTheory.integral_fintype` (Fintype 上の積分 = 有限和) | `Mathlib/MeasureTheory/Integral/Fintype.lean` | loogle `MeasureTheory.integral_fintype` |
| `Set.singleton_prod_singleton`: `{x} ×ˢ {y} = {(x,y)}` | `Mathlib/Data/Set/Prod.lean` | loogle `Set.singleton_prod_singleton` |
| `Measure.compProd_apply_prod` (Prod set への compProd 値) | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean` | loogle |
| `Measure.integral_compProd` (compProd 上の積分 = 二重積分) | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean` | loogle `MeasureTheory.Measure.integral_compProd` |
| Phase B reshape の主役 | `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean` `MeasurableEquiv.piFinSuccAbove` + `_apply` | loogle |
| Phase C reshape: `MeasurableEquiv.piCongrLeft` (index 同型で Pi を reshape) | 同上 | loogle |
| Phase C reshape: `MeasurableEquiv.sumPiEquivProdPi` (sum index → product Pi) | 同上 | loogle |
| Phase C reshape: `MeasurableEquiv.funUnique` (`Unit → α ≃ᵐ α`) | 同上 | loogle |
| Phase C 列挙: `Fin.sum_univ_castSucc` / `Fin.sum_univ_zero` | `Mathlib/Algebra/BigOperators/Fin.lean` | rg |
| Phase C base: `Pi.uniqueOfIsEmpty` (`Fin 0 → α` の `Unique`) | `Mathlib/Logic/IsEmpty.lean` | rg |

**「Mathlib に存在しなかった」もの (重要)**:

- **`MeasurableEquiv.piEquivPiSubtypeProd`** — 補集合 `{j : Fin n // j ≠ i}` を直接 `Fin i.val × {j // i < j}` に分けたい目的で loogle:
  - `MeasurableEquiv.piEquivPiSubtypeProd`
  - `MeasurableEquiv ((_ : Fin _ → _) → _) ((_ → _) × (_ → _))`
  - `Equiv.piEquivPiSubtype`
  - `{j : Fin _ // j < _} ≃ Fin _`
  - `MeasurableEquiv.piEquivPiSubtypeProd|MeasurableEquiv.piSplitAt` (rg)

  の 5 系統で空振り。`Equiv.piEquivPiSubtypeProd` は存在するが `MeasurableSpace` 版が無い (= `MeasurableEquiv` ではない)。**この不在が `exceptIdxEquiv` + `MeasurableEquiv.piCongrLeft` + `sumPiEquivProdPi` の 3 段経由を強制した**最大の単一要因。代替経路自体は素直 (sum 経由) だが、index 同型を手書きする ~50 行 + simp 駆動の Pi reshape ~95 行 が plumbing コストの大半を占めた。

- **`{j : Fin n // j ≠ i} ≃ Fin i.val ⊕ {j : Fin n // i < j}`** — 補集合の prefix/suffix 分解。
  - `Equiv.subtypeEquivRight`
  - `Subtype.subtypeEquivRight`
  - `Equiv.subtypeSubtypeEquivSubtypeInter`
  - `Fin.castLT`

  の 4 系統で空振り。**Mathlib に "ある index `i` を除いた `Fin n` の補集合を prefix と suffix に sum 分解する" `Equiv` は無い**。`exceptIdxEquiv` を手書き (~30 行)。`omega` と `Fin.ext` で `j.val < i.val` / `i.val ≤ j.val` の二分判定を書き下す。

- **`{j : Fin n // j ≠ i} ≃ Fin (n-1)` (基数同等)** — 補集合と `Fin (n-1)` の同型。これも見つからなかったが、本回は使わなかった (`exceptIdxEquiv` の sum 形のほうが Pi 値の reshape では自然だった)。textbook 公式では `Fin (n-1)` 版で書かれることが多いので、そちらを目指していたら詰まっていた可能性が高い。

- **`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ`** — Phase A 中間補題 (旧経路) で必要だった条件付き KL の積分公式。Phase 4-δ-(b) で同じく見つからなかった補題が、本回も Phase A 中間補題の **fiber 展開ルートを却下** (代わりに mutualInfo chain rule + Bridge × 2 経路) する原因になった。Phase 4-δ-(b) で同経路を経験していたため、本回は迷い時間を節約できた (= **過去 proof-log を読み返すツール** があれば「この経路は fiber 展開を諦める」を最初から判断できた)。

## 4. 試行錯誤と後戻り

### 4.1 Phase A 中間補題: fiber 展開ルートを却下

**症状**: skeleton 段階では「`condMutualInfo` を `klDiv_compProd_const_eq_lintegral_of_ac` (Bridge.lean Helper 1) で fiber 上に展開し、各 fiber で `mutualInfo_eq_entropy_sub_condEntropy` を呼ぶ」経路を計画していた (in `docs/han/han-moonshot-plan.md` §戦略)。

**原因**: `condMutualInfo` の compProd 形定義から `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` の per-fibre 展開公式が必要になるが、これは **Mathlib 不在 + 自作すると 50〜80 行**。Phase 4-δ-(b) で同じ壁に当たって却下した記憶を Phase 0 在庫調査時に拾っていた (`han-mathlib-inventory.md` で言及済)。

**抜け方**: 既存の `mutualInfo_chain_rule` (compProd 形 chain rule、Phase 4-δ-(b) で書いた) を出発点に、`mutualInfo_comm` × 2 + `condMutualInfo_comm` × 1 で第 1 引数を `Xs` に揃えてから `.toReal` を取り、Bridge 主定理 `mutualInfo_eq_entropy_sub_condEntropy` を 2 回呼んで `entropy μ Xs` を相殺する 4 段に切替。最終 ~30 行で完成。

**教訓**: 過去の proof-log で「この経路は Mathlib 不在で詰む」と記録した補題は、**新規ムーンショットの skeleton 設計時に自動引き当てされるべき**。本回は記憶頼りで運良く避けたが、半年後の自分は同じ穴に落ちる。将来のツール: 過去 proof-log の「Mathlib に存在しなかった」セクションを embedding 化して、新 skeleton の「想定経路」と照合するエージェント。

### 4.2 Phase A 中間補題: `ENNReal.toReal_add` の有限性が必要

**症状**: chain rule の ENNReal 等式 `mI(X; (Y,Z)) = mI(X; Y) + cMI(X; Z|Y)` から `.toReal` を取って Bridge を当てる段で、`(a + b).toReal = a.toReal + b.toReal` が成立するために **両辺の有限性 (`a ≠ ∞`, `b ≠ ∞`)** が必要。

**原因**: Mathlib `ENNReal.toReal_add` の signature がそうなっている。`mutualInfo_ne_top` / `condMutualInfo_ne_top` (= `klDiv ≠ ∞`) は本ファイルでは未整備だった (Phase 4-γ 時点では .toReal を相殺せずに ENNReal 上で linarith していた)。

**抜け方**: `MutualInfo.lean` に `mutualInfo_ne_top` を追加 (`Fintype` + `MeasurableSingletonClass` で `klDiv` の有限性を `klDiv_ne_top_iff` から導出、~10 行)、`CondMutualInfo.lean` に `condMutualInfo_ne_top` を追加 (前者を mutualInfo_chain_rule に逆代入、~10 行)。

**教訓**: ENNReal で組んだ ENNReal 等式から `.toReal` を取るパターンは Phase 4-γ / 4-δ-(b) / Han すべてで反復している。**`klDiv_ne_top` を使った `*_ne_top` lemma を主要 KL/entropy/MI 概念ごとに整備するか、専用 tactic** (`enn_toReal` のような) があると 30 分単位で節約できる。本回は loogle で `|- klDiv _ _ ≠ ⊤` を打って既存補題を探したが (`klDiv_ne_top_iff` を発見)、ad-hoc な finiteness lemma の作成までは自動化できていない。

### 4.3 Phase C: `MeasurableEquiv.piEquivPiSubtypeProd` の不在で plumbing が膨れる

**症状**: `Fin n → α` を `({j // j ≠ i} → α) × α` に分解する `MeasurableEquiv` を Mathlib から直接取りに行ったが空振り。さらに `({j // j ≠ i} → α)` を `(Fin i.val → α) × ({j // i < j} → α)` に分けるところでも空振り。

**原因**: Mathlib は `Equiv.piEquivPiSubtypeProd` (普通の `Equiv` 版) は持っているが、`MeasurableEquiv` 版は無い。可測性の観点では `Pi.MeasurableSpace` の構成 (`MeasurableSpace.pi`) の生成系が `eval i ⁻¹ s` であり、index が subtype に分かれた瞬間に「2 つの Pi の product space が元の Pi space と一致するか」を直接 morphism として確認する補題が必要だが、Mathlib にはそれが無い。

**抜け方**: 3 段 plumbing を自作:

```
Pi(Fin n)
  ↓ piCongrLeft (with fullIdxEquiv : Unit ⊕ {j // j ≠ i} ≃ Fin n)
Pi(Unit ⊕ {j // j ≠ i})
  ↓ sumPiEquivProdPi (sum index → product of Pi's)
Pi(Unit) × Pi({j // j ≠ i})
  ↓ funUnique (Unit → α ≃ᵐ α) on first factor
α × Pi({j // j ≠ i})
```

そして `Pi({j // j ≠ i})` の側を再度同じ 2 段 (`exceptIdxEquiv` で `Fin i.val ⊕ {j // i < j}` に分解 → `sumPiEquivProdPi`) で `Pi(Fin i.val) × Pi({j // i < j})` に分ける。合計で `MeasurableEquiv` を 3 本 (`exceptSplitMEquiv` / `piExceptMEquiv` / `fullSplitMEquiv`) + index 同型 2 本 (`exceptIdxEquiv` / `fullIdxEquiv`)。

**教訓**: `piEquivPiSubtypeProd` の `MeasurableEquiv` 版が Mathlib に上がっていれば、本回 plumbing は ~95 行から ~30 行 (= 単に `MeasurableEquiv` を一度 trans する) に圧縮できた。**Mathlib 投稿候補**として明確。将来のツール: Pi index の sum/subtype/product 分解で必要な `MeasurableEquiv` を自動構築するエージェント (`piCongrLeft` + `sumPiEquivProdPi` + `funUnique` の合成 boilerplate を出力)。

### 4.4 Phase C: Pi 値の reshape 後に `simp` で unfolding が stuck

**症状**: `fullSplitMEquiv i` を経由して `(Fin n → α) ≃ᵐ α × ((Fin i.val → α) × ({j // i < j} → α))` を構築した後、`(fun ω => fullSplitMEquiv i (fun j => Xs j ω)) = (fun ω => (Xs i ω, (prefix ω, suffix ω)))` の **pointwise 等価性を 1 回の `simp` で閉じようとしたら stuck**。`simp` が `MeasurableEquiv.trans` の中身を展開しきれない / `Equiv.piCongrLeft.symm` の `cast` が残る。

**原因**: `fullSplitMEquiv` は 3 段 trans + 1 個の `prodCongr` の合成で、各層に `MeasurableEquiv` ↔ `Equiv` の coe + `cast` 経由の `Equiv.piCongrLeft.symm` がある。`simp` の 1 回呼び出しでは展開順序が定まらず、`HEq` のまま残る項が出る。

**抜け方**: `Prod.ext` + `funext` で 3 成分 (= `α` 成分 / prefix `Fin i.val → α` 成分 / suffix `{j // i < j} → α` 成分) に分解し、**各成分ごとに `simp` を呼ぶ**。さらに simp lemma セットも component ごとに必要なものだけ列挙 (`prefSuff` / `pref` を first 成分で、`suff` を second 成分で、`α` 成分は何も追加要らず):

```lean
funext ω
apply Prod.ext
· apply Prod.ext
  · funext k
    simp [e_full, fullSplitMEquiv, piExceptMEquiv, exceptSplitMEquiv,
      fullIdxEquiv, exceptIdxEquiv, MeasurableEquiv.piCongrLeft,
      MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.funUnique,
      MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm,
      prefSuff, pref,
      Equiv.piCongrLeft, Equiv.sumPiEquivProdPi]
  · funext k
    simp [..., prefSuff, suff, ...]   -- suffix 用 simp set
· simp [..., prefSuff, ...]            -- α 成分用 simp set
```

**教訓**: 多段 `MeasurableEquiv.trans` の pointwise 計算は **成分ごとに分解 + 個別 simp** が安定。将来のツール: `MeasurableEquiv.trans` の合成等式を `Prod.ext` + `funext` の component-wise 分解 + `simp [...]` の simp lemma セットを auto-generate するタクティク。

### 4.5 Phase C: `set_option linter.unusedSectionVars false in` の配置順序

**症状**: `han_single_bound` / `han_inequality` で `[DecidableEq α]` instance を使うが Lean linter が「unused section variable」と誤検出する。`set_option linter.unusedSectionVars false in /-- doc -/ private lemma ...` と書いたら **「expected 'lemma'」でパースが壊れる**。

**原因**: `set_option ... in` は直後の宣言に attach するが、**docstring (`/-- ... -/`) も「宣言」扱いされる**。順序が `set_option in` → `docstring` → `private lemma` のとき、`set_option in` が docstring に attach してしまい、その後 `private lemma` が孤立する。

**抜け方**: 順序を入れ替え:

```lean
-- ❌ 壊れる
/-- 個別不等式: ... -/
set_option linter.unusedSectionVars false in
private lemma han_single_bound ...

-- ⭕ 通る
set_option linter.unusedSectionVars false in
/-- 個別不等式: ... -/
private lemma han_single_bound ...
```

**教訓**: **docstring は宣言の頭に置くのが Lean 4 の構文ルール**で、`set_option in` のような attribute 修飾子はその外側に置く。文法の細部だが、エラーメッセージ「expected 'lemma'」が出る位置が docstring の真上ではなく `set_option` の行を指すため、原因特定に 3〜5 分かかった。**linter / formatter で `set_option in` が docstring を貫通していないかを警告する**ルールが欲しい。

### 4.6 `[DecidableEq α]` が linter で「unused」と誤検出される

**症状**: Phase C の `han_single_bound` / `han_inequality` で `[DecidableEq α]` を section variable に置いて使うが、`linter.unusedSectionVars` が false-positive を出す。

**原因**: `[DecidableEq α]` は本体には現れないが、`Pi.decidableEq` / `Prod.decidableEq` / `Subtype.decidableEq` の **instance synthesis 経由で** `entropy_measurableEquiv_comp` 等の typeclass 要件を満たすのに使われる。Lean linter は instance 合成の連鎖を辿らないので「不使用」と判定する。

**抜け方**: `set_option linter.unusedSectionVars false in` で抑制 (各補題ごとに付ける、~3 ヶ所)。

**教訓**: **instance synthesis 経由で間接的に使われる typeclass argument を linter が認識する**機能が Mathlib / Lean 側に欲しい。Phase 4-α / 4-β でも同種の問題が起きていた (具体的には `[StandardBorelSpace _]`)。反復ボトルネック。

## 5. ボトルネックではなかったもの

- **数学のアイデア**: Han の証明骨格は教科書 (Cover & Thomas 17.6) 通り、新規アイデアゼロ。
- **Phase A chain rule 主体**: `compProd_map_condDistrib` + `Real.negMulLog_mul` + `integral_fintype` の 3 点セットで disintegration の calc が ~70 行で書け、ハマりなし。
- **Phase B induction**: `MeasurableEquiv.piFinSuccAbove` (Mathlib 既存) で `Fin (n+1) → α ≃ᵐ α × (Fin n → α)` が 1 行で出る。step ケースの組立てに **15 分程度** で完成 (ファイル末尾の chain rule proof 75 行のうち、reshape 部 30 行 + Phase A 適用 + IH 30 行 + sum_univ_castSucc 整形)。
- **Phase C 主定理 `han_inequality`**: `han_single_bound` が出来てしまえば 25 行で済んだ (`Finset.sum_le_sum` + `Finset.sum_sub_distrib` + `linarith`)。
- **退化ケース (n = 0, 1)**: 当初 `hn : 1 ≤ n` を仮定する想定だったが、実装してみると n = 0 で LHS = (-1)·0 = 0、RHS = 空和 = 0 で成立。`Pi.uniqueOfIsEmpty` で `Fin 0 → α` の `Unique` を引き出して entropy = 0 を出せたのが効いた。**hn 不要** が判明し statement から削除。
- **コンテキスト長**: 1M context で全 6 セッション余裕。Phase A の Bridge / MutualInfo / CondMutualInfo の 3 ファイルを同時に保持しながら Phase A 中間補題を組めた。
- **ツール失敗 (recoverable)**: 6 件 / 全 399 ツールコール。失敗が plumbing 進行のボトルネックにはなっていない。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **過去 proof-log の「Mathlib に存在しなかった」セクションを skeleton 設計時に自動照合**するエージェント | Phase A 中間補題の経路選択 (fiber 展開却下) を確信を持って即決できる。記憶頼り運に依存しない。Phase 4-δ-(b) と Han で同じ壁に 2 回当たっており、3 回目以降は完全に automatable |
| 高 | **`MeasurableEquiv` 経由の Pi index 分解 plumbing 自動生成**: `piCongrLeft` + `sumPiEquivProdPi` + `funUnique` の合成 boilerplate を、index 同型 (`exceptIdxEquiv` / `fullIdxEquiv`) を入力として吐く | Phase C の `MeasurableEquiv` 5 本 + index 同型 2 本 = ~95 行が ~30 行に圧縮できる |
| 高 | **多段 `MeasurableEquiv.trans` の pointwise 等価性を component-wise に解く tactic** (`apply Prod.ext; · funext ...; · simp [...]; ...` の boilerplate を auto-generate) | Phase C `han_single_bound` の Bridge 1 / Bridge 2 で打った component-wise simp = ~50 行が消える |
| 高 | **Mathlib 投稿候補の検出**: `MeasurableEquiv.piEquivPiSubtypeProd` のような「`Equiv` 版はあるが `MeasurableEquiv` 版がない」ケースを自動発見し、PR 化する | 未来の同種ムーンショットへの投資。本回は plumbing 95 行で済んだが、PR 化すれば Mathlib 全体の Pi reshape コストが下がる |
| 中 | **`klDiv ≠ ∞` / `entropy ≠ ∞` / `mutualInfo ≠ ∞` の `*_ne_top` 補題セット整備 + 専用 tactic** (`enn_toReal`?) | Phase A 中間補題で `mutualInfo_ne_top` / `condMutualInfo_ne_top` を新規追加 ~20 行。Phase 4 系列でも反復している |
| 中 | **subagent inventory の構造化テンプレート** (Phase 4-δ-(b) からの継続課題、CLAUDE.md に既反映): 補題ごとに `[type-class prereqs]` 必須欄。Han Phase 0 では既に「`Fin n → α` の instance チェイン」を明示的にチェックする項目を立てていたので機能した | Phase 0 から Phase A 着手までの不確実性削減。本回は機能 |
| 中 | **`set_option in` / docstring / `private` の構文順序を静的に検査する linter** | 4.5 のパース不能エラーを未然に防ぐ |
| 中 | **instance synthesis 経由で使われる typeclass argument を `linter.unusedSectionVars` が認識する**改善 (Mathlib / Lean 側修正) | `set_option linter.unusedSectionVars false in` の繰り返しが消える |
| 低 | **Pi 値 reshape の simp 駆動の安定化**: 各層 (`piCongrLeft`, `sumPiEquivProdPi`, `funUnique`) の simp lemma を 1 セット化し、order-independent に展開できる simp normal form | 4.4 の component-wise simp 列挙が縮む |

優先度の根拠: Pi 値 reshape (3 行 + 4 行) と過去 proof-log 引き当ては本セッションの **行数・時間・判断の支配項**。前者は機械的生成可能で還元先が明確、後者は「半年後の自分が落ちる穴」を埋める価値がある。

## 7. 補足

### 過去の proof-log との関係

- **Phase 4-δ-(b) との直接連続性**: 本回 Phase A 中間補題が `mutualInfo_chain_rule` / `condMutualInfo_comm` / `mutualInfo_comm` に依存し、これらは Phase 4-δ-(b) で書いた。**Phase 4-δ-(b) の plumbing 投資が Han Phase A の「fiber 展開ルート却下」を可能にした**。逆に Phase 4-δ-(b) の経験が無ければ本回は中間補題で 50〜80 行余計に書いていた。
- **`mutualInfo_ne_top` / `condMutualInfo_ne_top` の追加** は Phase 4-δ-(b) 時点では .toReal 相殺ではなく ENNReal 上 linarith で完走できていたため未整備だった。本回追加した形は将来のムーンショット (Slepian-Wolf converse 等) で .toReal 経由する場面で再利用できる。
- **`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` の per-fibre 展開公式不在** は Phase 4-δ-(b) と Han で同じ壁。3 度目で完全に "Mathlib 未整備、迂回前提" として skeleton 設計に組み込むべき (= ツール示唆 §6 高 1)。

### Phase 0 在庫調査の効果

`docs/han/han-mathlib-inventory.md` (Phase 0 出力) が機能した点:

- `Pi.fintype` / `MeasurableSpace.pi` / `Pi.instMeasurableSingletonClass` の自動発火確認 → Phase B / C で instance 合成に詰まらず
- 「Mathlib に Han / Shearer 不在」確定 → 自前 Han への直行を確信できた
- `condDistrib` / `compProd_map_condDistrib` の所在確認 → Phase A skeleton で経路選択を誤らず
- `klDiv per-fibre 展開公式 不在` 確認 → Phase A 中間補題で fiber ルートを skeleton 段階で却下できた

機能しなかった点:

- `MeasurableEquiv.piEquivPiSubtypeProd` 不在は Phase 0 では未調査 (Phase C で初めて判明)。Phase 0 は entropy / condDistrib 周辺をマップしたが Pi 値の `MeasurableEquiv` reshape 系は守備範囲外だった。**Phase 0 の網羅性を上げる**よりも、Phase C 着手時に **「これから書く plumbing の Mathlib 担保」を再確認するチェックポイント** を Phase B 終了時に挿入するほうが現実的。

### han_single_bound の最終形 (参考)

```lean
private lemma han_single_bound (μ Xs hXs i) :
    jointEntropy μ Xs - jointEntropyExcept μ Xs i
      ≤ condEntropy μ (Xs i) (prefix Xs i) := by
  -- 1. Phase A chain rule on (prefSuff, Xs i)
  --    h_chain : entropy μ (prefSuff, Xs i) = entropy μ prefSuff + condEntropy μ (Xs i) prefSuff
  -- 2. Bridge 1: entropy μ (prefSuff, Xs i) = jointEntropy μ Xs        (fullSplitMEquiv で 1:1)
  -- 3. Bridge 2: entropy μ prefSuff          = jointEntropyExcept μ Xs i (exceptSplitMEquiv で 1:1)
  -- 4. condEntropy_le_condEntropy_of_pair (Phase A): condEntropy μ (Xs i) prefSuff ≤ condEntropy μ (Xs i) prefix
  -- 5. linarith
```

ポイントは **Phase A の `entropy_pair_eq_entropy_add_condEntropy` (= chain rule) に流し込む形に Pi 値を整形する**ことが本回 plumbing の本質で、数学的内容は Phase A の主定理 1 本 + 「条件付けで減る」1 本 + 全部が Mathlib 既存 `Finset.sum_*` で閉じる。Phase A の投資が直接 Phase C の主定理を 25 行で出すことに繋がっている。

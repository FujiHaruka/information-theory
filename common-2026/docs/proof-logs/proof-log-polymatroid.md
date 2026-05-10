# Polymatroid Axioms (Submodularity of Entropy) Lean 形式化 — ボトルネック分析

`Common2026/Shannon/Polymatroid.lean` で entropy の **polymatroid rank function**
3 性質 ((i) `H(X_∅) = 0`、(ii) `S ⊆ T ⇒ H(X_S) ≤ H(X_T)`、(iii) submodularity
`H(X_{S∪T}) + H(X_{S∩T}) ≤ H(X_S) + H(X_T)`) を Lean 4 で証明した記録。本 proof-log
は質的観察に絞る (定量データは `scripts/session_metrics.ts` 任せ)。

## 0. 対象問題と成果物

**最終定理** (`Common2026/Shannon/Polymatroid.lean`):

```lean
theorem jointEntropySubset_empty
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) :
    jointEntropySubset μ Xs ∅ = 0

theorem jointEntropySubset_mono
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {S T : Finset (Fin n)} (h : S ⊆ T) :
    jointEntropySubset μ Xs S ≤ jointEntropySubset μ Xs T

theorem jointEntropySubset_submodular
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S T : Finset (Fin n)) :
    jointEntropySubset μ Xs (S ∪ T) + jointEntropySubset μ Xs (S ∩ T)
      ≤ jointEntropySubset μ Xs S + jointEntropySubset μ Xs T
```

成果物:

- `Common2026/Shannon/Polymatroid.lean` — 288 行、0 errors / 0 sorry / 0 warning
  - 主定理 3 本 (Phase A〜C)
  - 補助 helper 2 本 (再利用可):
    - `jointEntropySubset_disjoint_union` (`Disjoint s t` + `s ∪ t = U` で chain rule)
    - `condEntropy_reshape_disjoint_union` (conditioner 側 reshape)
  - private helper 1 本: `condEntropy_nonneg_local`
    (SlepianWolf.lean の `condEntropy_nonneg` と同一証明、依存方向が逆なので in-file で複製)
- `Common2026/Shannon/HanD.lean` — 既存 3 declarations (`subsetIdxEquiv`,
  `subsetSplitMEquiv`, `subsetSplitMEquiv_apply`) を `private` から **公開化**
  (Polymatroid.lean からの再利用のため)
- `Common2026.lean` に `import Common2026.Shannon.Polymatroid` 追記
- `docs/han/polymatroid-moonshot-plan.md` Phase A〜C ✅ + Phase D 判断ログ
- Phase D は **(D-b)「別 plan に切り出し」採用**、本 plan は core delivery で close

`lake env lean Common2026/Shannon/Polymatroid.lean` silent / `lake build` 全体緑通過
(2772 jobs)。

## 1. 問題のキャラクター

「**Han Phase D の `jointEntropySubset` を polymatroid の言葉で性質付ける、plumbing
支配型**」。本質的な不等式は条件付きエントロピーの単調性 (`condEntropy_le_condEntropy_of_pair`)
1 発で、それ以外は **Pi 値 reshape の plumbing** が支配項。

3 つの Phase はそれぞれ:

- **Phase A** — `(↥(∅ : Finset _) → α)` の trivialization。`Pi.uniqueOfIsEmpty` 一発。
  HanD chain rule base case (`Han.lean:64-85`) と完全に同じ流儀の写経。15 行。
- **Phase B** — `T = S ⊔ (T \ S)` reshape + chain rule + `condEntropy ≥ 0`。30 行。
- **Phase C** — 3 ピース disjoint 分解 `S ∪ T = (S∩T) ⊔ (S\T) ⊔ (T\S)`。helper 経由
  4 等式 + `condEntropy_le_condEntropy_of_pair` + `linarith` で着地。50 行。

## 2. ボトルネック分析

### 2.1 計画懸念 1 (3-piece Pi reshape) は `subst` 一発で消えた

事前 inventory で最大の不確実性とされていたのは **「Phase C の 3-piece reshape の
`MeasurableEquiv` cast まわり (`Disjoint`, `union` の associativity が effortlessly
通るか)」**。撤退ラインで `subsetSplit3MEquiv` 自前 (40〜60 行追加) を準備していた。

実装してみると、3 ピースを 1 発で reshape する必要はなく、**「2 つの disjoint
union を順次組み立てる」** 形で済むと判明:

- `S = (S∩T) ⊔ (S\T)` (1 段)
- `T = (S∩T) ⊔ (T\S)` (1 段)
- `S ∪ T = S ⊔ (T\S)` (1 段)

各段は `MeasurableEquiv.piFinsetUnion` 1 回 (= `subsetSplitMEquiv` 1 回) で済む。
**3 ピース化を 2 段の 2 ピース化に分解** したのが鍵。

そして cast 問題は **「`s ∪ t = U` を引数で受ける helper」** で吸収:

```lean
theorem jointEntropySubset_disjoint_union
    ... {s t U : Finset (Fin n)} (hd : Disjoint s t) (hU : s ∪ t = U) :
    jointEntropySubset μ Xs U
      = jointEntropySubset μ Xs s
        + InformationTheory.MeasureFano.condEntropy μ
            (fun ω (j : ↥t) => Xs j.val ω)
            (fun ω (j : ↥s) => Xs j.val ω)
```

ここで `subst htU` (`htU : U \ s = t`) を **proof script 内で発火** すると、
`↥(U \ s) → α` と `↥t → α` が **同一型** になり、cast が消える。`subst` は variable
`t` を `U \ s` で置換 (右辺の `t` は variable なので OK)。これだけで 3-piece
reshape の懸念が解消。**Finset 等式 cast 系の問題は、equality を `Eq.mpr` で消すより
`subst` で variable を置換する方が plumbing が劇的に軽い**。

### 2.2 `subsetSplitMEquiv` の private 解除を即決

inventory では「Mathlib `MeasurableEquiv.piFinsetUnion` を直接採用、HanD `subsetSplitMEquiv`
は private なので import 不可」と整理されていたが、実装してみると **両者は機能的に
完全等価** で、`subsetSplitMEquiv` の `T₁ ⊆ T₂` 形は subset chain rule との接続が
1 段ぶん軽い (Finset cast `S ∪ (T \ S) = T` を avoid できる)。

Polymatroid.lean からの再利用のために HanD.lean の以下 3 つの `private` を外した:

- `subsetIdxEquiv`
- `subsetSplitMEquiv`
- `subsetSplitMEquiv_apply`

公開化は **副産物として後続 moonshot (Slepian–Wolf 等) でも再利用可能** になる。
Mathlib `piFinsetUnion` をいちいち呼び出して disjoint 仮定を組み立てる手間が
省ける形で、本 project 内の Pi 値 reshape API として活用が見込める。

### 2.3 `condEntropy_nonneg` の所属問題

`SlepianWolf.lean:182` に `condEntropy_nonneg` がある (5 行の short proof:
`integral_nonneg + Finset.sum_nonneg + Real.negMulLog_nonneg`)。
Polymatroid → SlepianWolf は **依存方向が逆** (両者は並列のムーンショット) なので
import できない。

3 つの選択肢:

1. **Polymatroid 内に重複定義** (5 行の short proof なので低コスト)
2. **`Entropy.lean` に上流 lift** (SlepianWolf も Polymatroid も同じ補題を共有)
3. **`Pi.lean` に新規補題として追加**

最終的には (1) を採用 (`condEntropy_nonneg_local` という private theorem として
Polymatroid.lean 内に定義)。理由:

- short proof で重複コストが小さい
- 上流 lift (2/3) は本 plan のスコープを超える refactoring
- 後続で 3 番目の caller が現れたら (2) に格上げする方針

**観察**: 本 project の `Common2026/Shannon/` は moonshot ごとに **並列の枝** で
育っており、共通補題が下流で重複しがち。Slepian–Wolf 着手時に上流 lift を
検討するのが自然な timing。

## 3. 設計上の気づき

### 3.1 `disjoint_union` 形 helper が plumbing の天井を下げる

`jointEntropySubset_disjoint_union` (chain rule 形) と
`condEntropy_reshape_disjoint_union` (conditioner reshape 形) の 2 つの helper を
作っただけで、Phase C 本体は **50 行で linarith に着地** する。helper なしで
直接 `subsetSplitMEquiv` を Phase C 内で呼ぶと、Finset 等式 cast (`S \ (S∩T) = S\T` 等)
が 3 箇所同時に出現し、それぞれ別々に処理する羽目になる。

**helper の signature 設計**:

- `Disjoint s t` (素直な disjoint hypothesis)
- `s ∪ t = U` (target を 1 hypothesis で受け取る)
- 戻り値で `s` と `t` の subtype 形を直接返す (cast を helper 内で吸収)

この形なら caller 側は disjoint と union equality を Finset 補題で組み立てるだけで済み、
subtype cast を **1 度も書かずに** chain rule が使える。今後 Pi 値 reshape 系の
helper を増やすときは、

- 「`Disjoint` + 結果集合の equality」を引数で受け取る形
- helper 内で `subst` で変数を置換して cast を消す

の 2 パターンを優先する。

### 3.2 計画懸念 3 (Phase D scope creep) は適切に避けた

inventory 軸 1 で `Polymatroid` structure / 集合関数 `Submodular` structure が
Mathlib 不在なのは確認済 (Matroid rank の補題のみ)。本 plan で structure を導入
すると:

- 新規 `structure Polymatroid` の field 設計
- `noncomputable instance Polymatroid (jointEntropySubset μ Xs)` の組み立て
- 後続 moonshot (Seed 4 / Seed 5) での再利用シナリオの validation

の 3 点で時間を取られる。Phase A〜C の core delivery (3 性質単発 theorem) で
publish 価値は十分あるので、structure 化は **独立 plan として切り出す** ((D-b))。

判断時間: **Phase A〜C 完了後の 1 ターン以内**。Mathlib 不在裏取りが事前に済んで
いたので、判断材料は揃っていた。

## 4. 計画 vs 実装の対比

| Phase | 計画見積 (inventory 後) | 実装 |
|---|---|---|
| Phase A | 1〜2 日 / 15〜25 行 | 15 行 / 1 ターン以内 |
| Phase B | 2〜3 日 / 30〜50 行 | 30 行 / 1 ターン以内 |
| Phase C | 5〜7 日 / 150〜250 行 | 50 行 (本体) + helper 55 行 = 105 行 / 1 ターン以内 |
| Phase D | 0〜1 日 / 0〜40 行 | 0 行 ((D-b) 採用) |
| **合計** | **195〜365 行** | **288 行** |

**支配項**: Phase C の 3-piece 分解は計画懸念 1 の通り山場だったが、`subst`
1 発で cast 問題が消えたため、撤退ラインに用意していた `subsetSplit3MEquiv` 自前
拡張 (40〜60 行) は不要。**helper 設計**で plumbing を吸収できたのが効いた。

## 5. 後続への申し送り

- **`subsetIdxEquiv` / `subsetSplitMEquiv` / `subsetSplitMEquiv_apply` を `Pi.lean`
  に上流 lift する候補**: HanD.lean / Polymatroid.lean / 将来の Slepian–Wolf 等で
  再利用される。`Common2026/Shannon/Pi.lean` の Pi 値 reshape 補題 family に
  自然に収まる
- **`condEntropy_nonneg` を `Pi.lean` か `Entropy.lean` に上流 lift する候補**:
  Polymatroid.lean / SlepianWolf.lean で重複している 5 行 lemma。3 番目の caller
  が現れた時点で lift
- **`Polymatroid` structure 化 plan**: Mathlib upstream PR 候補。`Polymatroid` def +
  `Matroid.IsBase.toPolymatroid` (matroid rank → polymatroid) + 本 entropy 結果の
  インスタンス登録の 3 点をまとめて plan にする

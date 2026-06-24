# Shearer cover bundle (B-2 + B-9) ムーンショット計画 🌙

> オーケストレータ指示: B-2 (Hypercube edge isoperimetry / Han-Bregman) + B-9 (Brascamp-Lieb 組合せ形) を bundle 実装。
> 既存 `InformationTheory/Shannon/LoomisWhitney.lean` の Shearer 応用パターンを **任意 cover** に汎化。

## 進捗

- [x] Phase 0 — Mathlib inventory 📋 → [shearer-cover-bundle-inventory.md](shearer-cover-bundle-inventory.md)
- [x] Phase A — `entropy_le_log_image_card` の **汎用化版** を確認 (既存補題が cover に非依存、再利用のみ) ✅
- [x] Phase B — Brascamp-Lieb (一般化 LW): `|A|^k ≤ ∏ i, |π_{S_i}(A)|` ✅
- [x] Phase C — Hypercube edge isoperimetry / Han-Bregman 系の corollary (singleton cover + edge bound) ✅
- [x] Phase D — LW refactor 判断 (見送り、既存 statement 維持) 🔄

> **実態整合 (2026-05-20): DONE-UNCOND (publish 済、0 sorry、plan は正確)** —
> `InformationTheory/Shannon/BrascampLieb.lean` が実在: `projectionSubset` (`:40`)、subset-entropy bound
> `jointEntropySubset_le_log_projectionSubset_card` (`:52`)、主定理 `brascamp_lieb_finset`
> (`:90`、`A.card ^ k ≤ ∏ i, (projectionSubset (S i) A).card`) はいずれも genuine `by`-proof
> (Shearer + `uniformOn` 経由、pass-through なし)、`rg -nw sorry` 空振り。Phase A-D の `[x]` は実態と一致、修正不要。

## ゴール / Approach

3 件 (LW / Brascamp-Lieb / Hypercube isoperimetry) を **共通 tooling = Shearer + entropy_le_log_image_card** の上に並べる。

**Approach**:

1. **既存 `entropy_le_log_image_card` は cover 非依存** — `uniformOn A` 上で `f : (Fin n → α) → γ` が任意なら `entropy μ f ≤ log #(A.image f)`。これは LW 専用ではなく、任意 projection 用の補題。よって **新規補題を追加せず**、`BrascampLieb.lean` から再利用する。
2. **`projectionSubset`** 新規定義: `S : Finset (Fin n)` に対して `A.image (fun x j : ↥S => x j.val)` = `S` 制限射影像。LW の `projectionExcept` の **任意 S 版**。
3. **`jointEntropySubset_le_log_projectionSubset_card`**: 任意 `S` 上の subset-entropy ≤ projection image の log。`jointEntropySubset_le_log_projectionExcept_card` を `S = univ.filter (· ≠ i)` から **任意 S** に reshape (同型構造はそのまま、`piCongrLeft` で `↥S → α` ↔ `S` 元の dependent function に詰め替えるだけ)。
4. **Brascamp-Lieb main**: `μ := uniformOn A`, `Xs i ω := ω i`, Shearer 適用、両辺 log を bridge し log を剥がして自然数版へ。**LW と同じパターンで cover だけ任意化**。
5. **Hypercube isoperimetry corollary**: singleton cover `S_i := {i}` (各 j を 1 回 cover) で BL は `|A| ≤ ∏ i, |π_{i}(A)|` (= 各成分の像の積) を与える。これは Han-Bregman bound の最も基本形。`α = Bool` を取ると Boolean cube 上の積上界として読める。

**LW refactor は見送り** (Phase D 判断ログ参照): 既存 `loomis_whitney` のシグネチャは下流に晒されないが (`InformationTheory.lean` import のみ)、ローカル証明を一掃するメリットは薄く、新規 `brascamp_lieb_finset` の存在で十分。LW は `S i := univ.filter (· ≠ i)` の特殊形として **理論的に** corollary だが、**Lean ファイル上は独立** に保つ。

## Phase 0 - Mathlib inventory ✅

- loogle で `Brascamp` / `edgeBoundary` / `BooleanCube` / `loomis` / `hypercube` を検索 → 全件 0 件 (Mathlib に既存なし)。
- 既存 `HanDShearer.shearer_inequality` のシグネチャ確認: 任意 `ι` (Fintype) と `S : ι → Finset (Fin n)`、cover 条件 `∀ i, k ≤ #(univ.filter (i ∈ S j))` で `k * H ≤ ∑ H_{S_j}`。**そのまま再利用可能**。

## Phase A - tooling 確認 ✅

LW の `entropy_le_log_image_card` (LoomisWhitney.lean:125) は **既に汎用** (任意 measurable `f : β → γ`)。よって新規 helper は不要、Phase A は補題追加なし。

`projectionSubset {n : ℕ} {α} [DecidableEq α] (S : Finset (Fin n)) (A : Finset (Fin n → α))` :=
  `A.image (fun x (j : ↥S) => x j.val)` を `BrascampLieb.lean` に新規定義。

## Phase B - Brascamp-Lieb main 🚧

主定理シグネチャ (Lean):

```
theorem brascamp_lieb_finset
    {n k : ℕ} {ι : Type*} [Fintype ι]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Finset (Fin n → α)} (hA : A.Nonempty)
    (S : ι → Finset (Fin n))
    (hk : ∀ j : Fin n, k ≤ (Finset.univ.filter (fun i : ι => j ∈ S i)).card) :
    A.card ^ k ≤ ∏ i : ι, (projectionSubset (S i) A).card
```

ステップ:
- [x] `projectionSubset` 定義
- [x] `jointEntropySubset_le_log_projectionSubset_card` (任意 S 版)
- [x] Shearer 適用 + log bridge + log 剥ぎ (LW pattern)
- [x] `lake env lean InformationTheory/Shannon/BrascampLieb.lean` silent 通過

## Phase C - Hypercube edge isoperimetry corollary ✅

singleton cover `S i := {i}` で Brascamp-Lieb は `|A| ≤ ∏ i, |π_{i}(A)|` を与える。これを `hypercube_product_projection_bound` として corollary 化。

`α = Bool` (Boolean cube) を渡せば `|π_i(A)| ≤ 2` なので `|A| ≤ 2^n` (自明)。**より有用な形**は: Han-Bregman 系の `|A|^{n-1} ≤ ∏_i |π_{-i}(A)|` (= LW) との重ね合わせで edge boundary の bound を出すが、Mathlib に `SimpleGraph.edgeBoundary` の Boolean cube 形が存在しないため、本 plan ではここまでで stop (corollary の statement を `projectionSubset {i}` 形に絞り、edge boundary の独立形式化は B-2' deferred として切り出した)。

**B-2' edge-boundary 形 完了 (2026-05-12)** → [hypercube-edge-boundary-plan.md](hypercube-edge-boundary-plan.md): Boolean cube 上の coordinate-flip pair で `edgeBoundaryCount A` を直接組合せ的に定義し, counting identity `|∂_e A| + n |A| = 2 Σ |π_{≠i}(A)|` + LW + AM-GM で `2n · |A|^{(n-1)/n} ≤ |∂_e A| + n |A|` を `InformationTheory/Shannon/HypercubeEdgeBoundary.lean` (692 行) に publish 完了。`SimpleGraph` 構造は持ち込まず, `Sym2` も回避。

## Phase D - LW refactor 判断 🔄 (見送り)

判断: **LW は既存形を維持**。`brascamp_lieb_finset` (任意 cover 版) を `BrascampLieb.lean` に独立に置き、LW を corollary として書き直さない。理由:

1. `LoomisWhitney.loomis_whitney` のシグネチャは既に下流 (InformationTheory.lean の import 順) に展開済み。
2. BL から LW を導く re-proof は 10-20 行で書けるが、既存 LW 証明 (444 行) を消すと history を見失う。新規 `BrascampLieb.lean` (BL + Hypercube corollary) と並立させる方が clean。
3. `entropy_le_log_image_card` は **LoomisWhitney.lean に既存** で公開 namespace `InformationTheory.Shannon.entropy_le_log_image_card` として `BrascampLieb.lean` から `import InformationTheory.Shannon.LoomisWhitney` 経由で再利用可能。

## 判断ログ

1. **Phase 0 起草時**: Hypercube edge isoperimetry の target 形を loogle で確認したが、Mathlib に `edgeBoundary`/`BooleanCube` 既存なし。Cover-Thomas Ch 17 流の Han-Bregman bound (edge-boundary との比較) は **Boolean cube 構造の Lean 実装** が必要で本 bundle のスコープ外。Phase C は `singleton cover BL corollary` (= `|A| ≤ ∏ |π_i(A)|`) に縮小し、edge boundary 形は B-2 deferred として切り出す。
2. **Phase D**: LW refactor は見送り。新規 `BrascampLieb.lean` と既存 `LoomisWhitney.lean` を並立。

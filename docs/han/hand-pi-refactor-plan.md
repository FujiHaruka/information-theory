# HanD / Pi reshape refactor: `MeasurableEquiv.piFinsetUnion` 統合 計画 🧹

> 実態整合 (2026-05-20): DONE (Phase 1〜4 + 判断ログの追加撤去まで完了)。`InformationTheory/Shannon/Pi.lean` から `subsetIdxEquiv` は完全消失 (`rg` 0 hits)、subset-form `subsetSplitMEquiv` も撤去済。現存 API は `subsetSplitMEquivAux` (`Pi.lean:160`) + `MeasurableEquiv.piFinsetUnion_apply_left/right` (`Pi.lean:138,148`) に集約。`lake env lean InformationTheory/Shannon/Pi.lean` silent。これは refactor plan で新規 headline thm なし。
> **Status (2026-05-11)**: 起草。Polymatroid moonshot (`docs/han/polymatroid-moonshot-plan.md`)
> 完了直後の **C 横断改善** ([`docs/moonshot-seeds.md` §C](../moonshot-seeds.md))
> から派生。ムーンショット級の新規証明ではなく、**plumbing tightening** (= 自前
> `MeasurableEquiv` を Mathlib 上流補題で subsume する保守 refactor)。
>
> ゴールは `InformationTheory/Shannon/Pi.lean` 内の自前 `subsetIdxEquiv` /
> `subsetSplitMEquiv` / `subsetSplitMEquiv_apply` (合計 50+ 行) を Mathlib
> `MeasurableEquiv.piFinsetUnion` ベースに書き直し、call site (HanD ×1 +
> Polymatroid ×3) を破壊しないこと。

## 進捗

- [x] Phase 0 — Mathlib インベントリ ✅ → [`hand-pi-refactor-inventory.md`](hand-pi-refactor-inventory.md)
- [ ] Phase 1 — Pi.lean に Mathlib ベースの薄いラッパーを追加 (subset-form ヘルパー + `_apply_left/right` bridge) 📋
- [ ] Phase 2 — Polymatroid 内 `disjoint_union` ヘルパー 2 本を Mathlib 直接呼び出しに書き換え 📋
- [ ] Phase 3 — bespoke `subsetIdxEquiv` / 自前 `subsetSplitMEquiv` 内部実装を撤去 (API は subset-form ラッパーで温存) 📋
- [ ] Phase 4 — 全 caller の `lake env lean` re-verify + 行数 / warning 確認 📋

## ゴール / Approach

**ゴール (1〜2 行)**: `InformationTheory/Shannon/Pi.lean` の自前 reshape 補題 (`subsetIdxEquiv` / `subsetSplitMEquiv` / `subsetSplitMEquiv_apply`、合計 50+ 行) を Mathlib `MeasurableEquiv.piFinsetUnion` ベースの薄い (5〜15 行) ラッパーに置換する。HanD `condEntropy_subset_anti` と Polymatroid 3 主定理 (`jointEntropySubset_mono` / `jointEntropySubset_disjoint_union` / `condEntropy_reshape_disjoint_union`) は `lake env lean` で 0 sorry / 0 error を維持する。

### Approach (戦略の shape — 全体)

**Mathlib `MeasurableEquiv.piFinsetUnion` は drop-in ではない** (premise が `Disjoint s t` で conclusion が `↥(s ∪ t) → α`、bespoke は `T₁ ⊆ T₂` で `↥T₂ → α`)。よって素朴に call site を書き換えると 4 ヶ所で `Disjoint`/`union` の cast を毎度書くことになる。代わりに以下の 2 段ストラテジーを取る:

1. **Pi.lean 側で「subset-form ラッパー」を維持**: 既存 API (`subsetSplitMEquiv (h : T₁ ⊆ T₂)`) と同じシグネチャを保ち、内部実装だけを Mathlib `MeasurableEquiv.piFinsetUnion` + `Finset.disjoint_sdiff` + `Finset.union_sdiff_of_subset` に切り替える。これで HanD `condEntropy_subset_anti` と Polymatroid `jointEntropySubset_mono` の call site は **無変更**。

2. **Polymatroid 側「disjoint_union ヘルパー」は Mathlib 直接呼び出しに簡略化**: `jointEntropySubset_disjoint_union` / `condEntropy_reshape_disjoint_union` は引数で `Disjoint s t` + `s ∪ t = U` を受けているので、bespoke subset-form を経由する必要がない。`MeasurableEquiv.piFinsetUnion` を直接呼び、`subst hU` 一発で cast を消す形に書き直す。

この 2 段により:
- 自前 `subsetIdxEquiv` (= 25 行) は **削除**
- 自前 `subsetSplitMEquiv` 実装 (= 5 行) は **5 行のラッパーに置換** (def 自体は残す)
- 自前 `subsetSplitMEquiv_apply` (= 30 行) は **5〜10 行に縮小** (Mathlib `Equiv.piFinsetUnion_left/right` を経由)
- Polymatroid 内の 2 ヘルパーは各 5〜10 行短縮
- **総減: 30〜45 行**、Mathlib への依存度向上、HanD の call site 無変更

### Approach (per-phase)

- **Phase 1** (Pi.lean に薄いラッパー追加): まず Mathlib の `MeasurableEquiv.piFinsetUnion` の coe が `Equiv.piFinsetUnion` に defeq に等しいことを確認 (`coe_piFinsetUnion : ⇑(MeasurableEquiv.piFinsetUnion h) = Equiv.piFinsetUnion _ h := rfl` を 1 行の lemma として書く)。これを基に `MeasurableEquiv.piFinsetUnion_apply_left/right` を `Equiv` 版から 2 行で導出。subset-form `subsetSplitMEquiv` も別 `def` として残し、内部実装を Mathlib + cast に書き換え。**この Phase で `subsetIdxEquiv` はまだ残す** (Phase 3 で削除)。
- **Phase 2** (Polymatroid 直接化): Polymatroid 内 2 ヘルパーの内部実装を `MeasurableEquiv.piFinsetUnion` 直接呼び出しに書き換え、`subst hU` で cast を吸収。**Polymatroid の API シグネチャは無変更**。
- **Phase 3** (撤去): Pi.lean から `subsetIdxEquiv` を削除 (Phase 1 の subset-form `subsetSplitMEquiv` 内部実装が Mathlib ベースに切り替わっているはず)。古い `subsetSplitMEquiv_apply` の自前 50 行 proof は Phase 1 で薄い proof に置換済。
- **Phase 4** (verify): HanD.lean / Pi.lean / Polymatroid.lean を `lake env lean` で個別検証、行数比較、warning 確認。

ファイル変更マップ:

```
InformationTheory/Shannon/
  Pi.lean              ← 内部実装書き換え (subsetIdxEquiv 削除、subsetSplitMEquiv 薄化、apply lemma 短縮)
  HanD.lean            ← 無変更 (call site は subset-form ラッパー経由)
  Polymatroid.lean     ← 内部実装書き換え (disjoint_union 系 2 本のみ。本体 submodular は無変更)
```

## Phase 0 — Mathlib インベントリ ✅

サブ計画: [`hand-pi-refactor-inventory.md`](hand-pi-refactor-inventory.md)

調査軸 4 つ全て完了:

- [x] **軸 1: `MeasurableEquiv.piFinsetUnion` の存在と verbatim 形** — ✅ 存在確認 (`Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:612`)。premise = `Disjoint s t`, conclusion = `↥(s ∪ t) → α`
- [x] **軸 2: `Equiv.piFinsetUnion` 系 apply lemma** — ✅ `_left` / `_right` 両方存在 (`Mathlib/Data/Finset/Basic.lean:641-654`)。`MeasurableEquiv` 版用 `coe` lemma は不在 → Pi.lean に薄いブリッジを追加
- [x] **軸 3: Subset-from-Disjoint 橋渡し** — ✅ `Finset.disjoint_sdiff` + `Finset.union_sdiff_of_subset` で 2 行
- [x] **軸 4: 既存 call site の数と shape** — ✅ 4 ヶ所、全て同 pattern。HanD ×1 (subset form), Polymatroid ×3 (うち 2 ヶ所は disjoint+union form)

## Phase 1 — Pi.lean に Mathlib ベースの薄いラッパーを追加 📋

ターゲット: `InformationTheory/Shannon/Pi.lean` 内の自前 plumbing を Mathlib `MeasurableEquiv.piFinsetUnion` 上に再構築。subset-form API (`subsetSplitMEquiv (h : T₁ ⊆ T₂)`) は維持。

### スコープ (Pi.lean に追加 / 書き換える宣言)

```lean
-- 新規追加 (薄い coe lemma): MeasurableEquiv 版の coe が Equiv 版に等しい
@[simp] lemma MeasurableEquiv.coe_piFinsetUnion
    {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {s t : Finset ι} (h : Disjoint s t) :
    ⇑(MeasurableEquiv.piFinsetUnion (π := β) h) = Equiv.piFinsetUnion β h := rfl

-- 新規追加 (薄い apply lemma): Equiv.piFinsetUnion_left を MeasurableEquiv 版に持ち上げ
lemma MeasurableEquiv.piFinsetUnion_apply_left
    {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {s t : Finset ι} (h : Disjoint s t) (f : ↥s → β _) (g : ↥t → β _)
    {i : ι} (hi : i ∈ s) (hi' : i ∈ s ∪ t) :
    MeasurableEquiv.piFinsetUnion h (f, g) ⟨i, hi'⟩ = f ⟨i, hi⟩ := by
  rw [MeasurableEquiv.coe_piFinsetUnion]; exact Equiv.piFinsetUnion_left _ h hi hi'

-- 同 _right 版 (省略、_left と対称)

-- 書き換え (subset-form ラッパー): API シグネチャは温存、内部だけ Mathlib + cast
def subsetSplitMEquiv {n : ℕ} {T₁ T₂ : Finset (Fin n)} (h : T₁ ⊆ T₂) :
    ((↥T₁ → α) × (↥(T₂ \ T₁) → α)) ≃ᵐ (↥T₂ → α) :=
  let ePi := MeasurableEquiv.piFinsetUnion (π := fun _ : Fin n => α) Finset.disjoint_sdiff
  -- ePi : ((↥T₁ → α) × (↥(T₂ \ T₁) → α)) ≃ᵐ (↥(T₁ ∪ (T₂ \ T₁)) → α)
  -- cast (↥(T₁ ∪ (T₂ \ T₁)) → α) ≃ᵐ (↥T₂ → α) via Finset.union_sdiff_of_subset h
  ePi.trans (MeasurableEquiv.cast (by rw [Finset.union_sdiff_of_subset h]) (by ...))
  -- ↑ MeasurableEquiv.cast は Mathlib 既存。無ければ piCongrLeft で代替

-- 書き換え (subset-form apply): Mathlib _left/_right を経由した 5〜10 行
omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma subsetSplitMEquiv_apply
    {n : ℕ} {T₁ T₂ : Finset (Fin n)} (h : T₁ ⊆ T₂) (Xs : Fin n → α) :
    subsetSplitMEquiv (α := α) h
      (fun j : ↥T₁ => Xs j.val, fun j : ↥(T₂ \ T₁) => Xs j.val)
      = fun j : ↥T₂ => Xs j.val := by
  funext k
  obtain ⟨j, hj⟩ := k
  -- subsetSplitMEquiv = piFinsetUnion ∘ cast。cast は ↥T₂ ≅ ↥(T₁ ∪ (T₂\T₁)) なので
  -- by_cases h₁ : j ∈ T₁ で _left / _right を呼ぶ
  by_cases h₁ : j ∈ T₁
  · -- _left branch: 中の f = (fun j : ↥T₁ => Xs j.val), 結果 = f ⟨j, h₁⟩ = Xs j
    sorry  -- Phase 1 で実装
  · -- _right branch
    have hj₂ : j ∈ T₂ \ T₁ := Finset.mem_sdiff.mpr ⟨hj, h₁⟩
    sorry  -- Phase 1 で実装
```

### 鍵となる作業

- [ ] `MeasurableEquiv.coe_piFinsetUnion` を 1 行 (`rfl`) で書き、smoke test (`lake env lean InformationTheory/Shannon/Pi.lean`)
- [ ] `MeasurableEquiv.piFinsetUnion_apply_left` / `_right` を 2〜4 行ずつで Equiv 版から導出
- [ ] subset-form `subsetSplitMEquiv` 内部を Mathlib + cast に書き換え。`MeasurableEquiv.cast` の入手 (Mathlib 既存) または `piCongrLeft` 経由で代替する判断
- [ ] subset-form `subsetSplitMEquiv_apply` 内部を Mathlib `_left/_right` 経由に書き換え (5〜15 行に圧縮)
- [ ] `subsetIdxEquiv` は **Phase 1 ではまだ残す** (Phase 3 で削除、ただし Phase 1 後の subset-form 実装が Mathlib ベースになっているので未参照になる予定)

### Done 条件

- `lake env lean InformationTheory/Shannon/Pi.lean` が silent (0 error / 0 sorry / 既存 warning レベル維持)
- `lake env lean InformationTheory/Shannon/HanD.lean` も silent (call site 無変更で動作することを確認)
- 新規 lemma `coe_piFinsetUnion` / `piFinsetUnion_apply_left/_right` が Pi.lean docstring に追加 (任意)
- 行数: Pi.lean は **+10 〜 -20 行 (cast/apply 実装の出来による)**

### 工数感

1〜2 日 (50〜100 行修正)。`MeasurableEquiv.cast` の入手周りで多少詰まる可能性あり。詰まったら subset-form ラッパーは `subsetSplitMEquiv` の自前 def を維持したまま `subsetSplitMEquiv_apply` 内側だけを `_left/_right` で書き直す mini-refactor に縮退 (Phase 3 範囲も縮退)。

### 撤退ライン

- `MeasurableEquiv.cast` (or piCongrLeft cast) で `↥(T₁ ∪ (T₂ \ T₁)) ≅ ↥T₂` の橋渡しが defeq で潰れない → `subsetSplitMEquiv` 内部実装は維持、`subsetSplitMEquiv_apply` の中身だけを `_left/_right` を呼ぶ形に書き直し (実装 50 行 → 20 行) で部分達成

## Phase 2 — Polymatroid 内 `disjoint_union` ヘルパーを Mathlib 直接化 📋

ターゲット: `InformationTheory/Shannon/Polymatroid.lean` の `jointEntropySubset_disjoint_union` (line 123) と `condEntropy_reshape_disjoint_union` (line 166) の **内部実装** を Mathlib `MeasurableEquiv.piFinsetUnion` 直接呼び出しに書き換え。**API シグネチャは無変更**。

### スコープ (Polymatroid.lean 内の書き換え)

```lean
theorem jointEntropySubset_disjoint_union
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {s t U : Finset (Fin n)} (hd : Disjoint s t) (hU : s ∪ t = U) :
    jointEntropySubset μ Xs U
      = jointEntropySubset μ Xs s
        + InformationTheory.MeasureFano.condEntropy μ
            (fun ω (j : ↥t) => Xs j.val ω)
            (fun ω (j : ↥s) => Xs j.val ω) := by
  set XS : Ω → (↥s → α) := fun ω j => Xs j.val ω
  set XT : Ω → (↥t → α) := fun ω j => Xs j.val ω
  have hXS_meas : Measurable XS := measurable_pi_iff.mpr (fun _ => hXs _)
  have hXT_meas : Measurable XT := measurable_pi_iff.mpr (fun _ => hXs _)
  -- 直接 Mathlib piFinsetUnion (Disjoint s t) を呼ぶ
  let e := MeasurableEquiv.piFinsetUnion (π := fun _ : Fin n => α) hd
  -- e : ((↥s → α) × (↥t → α)) ≃ᵐ (↥(s ∪ t) → α)
  -- bridge: e (XS ω, XT ω) ⟨j, hj⟩ = Xs j ω
  have hbridge : (fun ω => e (XS ω, XT ω))
      = fun ω (j : ↥(s ∪ t)) => Xs j.val ω := by
    funext ω; funext ⟨j, hj⟩
    by_cases hjs : j ∈ s
    · have hj' : j ∈ s ∪ t := Finset.mem_union.mpr (Or.inl hjs)
      rw [MeasurableEquiv.piFinsetUnion_apply_left hd XS _ hjs hj']  -- Phase 1 で書いた lemma
      rfl
    · have hjt : j ∈ t := (Finset.mem_union.mp hj).resolve_left hjs
      rw [MeasurableEquiv.piFinsetUnion_apply_right hd _ XT hjt hj]
      rfl
  -- subst hU で (↥(s ∪ t) → α) ↔ (↥U → α) を吸収
  subst hU
  unfold jointEntropySubset
  rw [show (fun ω (j : ↥(s ∪ t)) => Xs j.val ω) = fun ω => e (XS ω, XT ω) from hbridge.symm]
  rw [entropy_measurableEquiv_comp μ (fun ω => (XS ω, XT ω))
        (hXS_meas.prodMk hXT_meas) e]
  exact entropy_pair_eq_entropy_add_condEntropy μ XS XT hXS_meas hXT_meas
```

`condEntropy_reshape_disjoint_union` も同 pattern (条件側 reshape)。

### 鍵となる作業

- [ ] `jointEntropySubset_disjoint_union` の内部を `subsetSplitMEquiv (hsU : s ⊆ U)` 経由から `MeasurableEquiv.piFinsetUnion hd` 直接呼び出しに書き換え。`subst hU` の方向が現状 `subst htU` から `subst hU` に変わる点に注意
- [ ] `condEntropy_reshape_disjoint_union` 同
- [ ] Polymatroid 内 `jointEntropySubset_mono` (Site 2) は **subset 形 API** を使っており Phase 1 で subset-form ラッパーが温存されているので **無変更** の見込み。ただし、もし `disjoint_union` ヘルパーで完全に置換できる (`hd := Finset.disjoint_sdiff`, `hU := Finset.union_sdiff_of_subset h` で 2 行追加して呼ぶ) なら `subsetSplitMEquiv` の subset-form 直接呼び出しを撤去する選択肢もあり (Polymatroid 単独での自己充足度向上)
- [ ] `jointEntropySubset_submodular` (本体) は `disjoint_union` ヘルパーを呼んでいるだけなので **完全無変更**

### Done 条件

- `lake env lean InformationTheory/Shannon/Polymatroid.lean` が silent (0 error / 0 sorry)
- 行数: Polymatroid.lean は **-10 〜 -20 行** (`htU` derive とかの中間 step が消える)
- `jointEntropySubset_submodular` の本体 proof は完全無変更 (回帰なし)

### 工数感

1〜2 日 (50〜80 行修正)。Phase 1 の `_apply_left/_right` lemma が動いていれば proof bottleneck はほぼゼロ、`subst hU` 経由で cast が一発で消えるかが唯一の不確実性。

### 撤退ライン

- `subst hU` 一発で cast が消えない → `(↥(s ∪ t) → α) → (↥U → α)` の `MeasurableEquiv.cast` を chain。+ 5 行
- Polymatroid `disjoint_union` ヘルパーが Mathlib 直接化で複雑化する → **Phase 2 を skip** し、Phase 1 で subset-form ラッパーだけ Mathlib 化、Polymatroid は subset-form 経由を維持 (現状維持)。Pi.lean の行数削減はそれでも達成

## Phase 3 — `subsetIdxEquiv` + subset 形 `subsetSplitMEquiv` の撤去 📋

ターゲット: Phase 1 / 2 後、`subsetIdxEquiv` および subset 形
`subsetSplitMEquiv` / `subsetSplitMEquiv_apply` が Pi.lean 内のどこからも
参照されなくなったら削除。subset 形は call site 2 ヶ所
(HanD `condEntropy_subset_anti` / Polymatroid `jointEntropySubset_mono`) を
`subsetSplitMEquivAux` 直接呼び出しに書き換えれば撤去可能 (+2 行/site)。

### 鍵となる作業

- [x] `rg "subsetIdxEquiv" InformationTheory/` で 0 件確認
- [x] `subsetIdxEquiv` def を削除
- [x] subset 形 `subsetSplitMEquiv` / `subsetSplitMEquiv_apply` を撤去し
  call site 2 ヶ所を `subsetSplitMEquivAux` 直接呼び出しに改修
  (`Finset.disjoint_sdiff` + `Finset.union_sdiff_of_subset h` を inline)
- [x] Pi.lean docstring から subset 形への言及を削除、aux 集約方針を明記
- [x] `lake env lean InformationTheory/Shannon/{Pi,HanD,Polymatroid,SlepianWolf}.lean`
  全て silent

### Done 条件

- Pi.lean から `subsetIdxEquiv` def + 関連 docstring が削除済
- Pi.lean から subset 形 `subsetSplitMEquiv` / `subsetSplitMEquiv_apply` が削除済
- 全 caller (HanD / Polymatroid / SlepianWolf) が `lake env lean` で silent
- 行数: 詳細は判断ログ (-12 net 行 達成、当初目標 -25 には届かず)

### 工数感

0.5 日 (25 行削除 + docstring 更新)。

### 撤退ライン

- もし Phase 1 で subset-form `subsetSplitMEquiv` の Mathlib ベース化に失敗していて `subsetIdxEquiv` がまだ参照されていたら、本 Phase は **skip** (Phase 1 撤退ライン に連動)

## Phase 4 — 全 caller の `lake env lean` re-verify + 行数 / warning 確認 📋

### 鍵となる作業

- [ ] `lake env lean InformationTheory/Shannon/Pi.lean` (silent)
- [ ] `lake env lean InformationTheory/Shannon/HanD.lean` (silent)
- [ ] `lake env lean InformationTheory/Shannon/Polymatroid.lean` (silent)
- [ ] (任意) `lake env lean InformationTheory/Shannon/SlepianWolf.lean` — Pi.lean を import している ([`docs/moonshot-seeds.md` §C](../moonshot-seeds.md) に記載) ので念のため確認
- [ ] (任意) `lake build InformationTheory.Shannon.Polymatroid` で olean 再生成、依存先全体に effect が無いことを smoke test
- [ ] 行数差分: `git diff --stat InformationTheory/Shannon/{Pi,HanD,Polymatroid}.lean` で実測 vs 見積比較

### Done 条件

- 全関係 file が `lake env lean` で silent
- 行数差分が見積 (-30 〜 -45 行) と整合
- warning 数の増加なし

### 工数感

0.5 日 (検証 + 数値比較のみ)。

## 失敗判定 / 撤退ライン

- **Phase 1 で `MeasurableEquiv.coe_piFinsetUnion : rfl` が通らない** → `Equiv.piFinsetUnion_left` を直接 invoke せず、Pi.lean 側で proof を `simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, ...]` 経由に書き直し (Mathlib `Equiv.piFinsetUnion_left` 内部の proof tactic を写経)。+15 行で吸収
- **Phase 1 で `subsetSplitMEquiv` 内部の cast が defeq でなく `MeasurableEquiv.cast` も使えない** → subset-form `subsetSplitMEquiv` は **自前 def を維持** し、`subsetSplitMEquiv_apply` の proof 内側だけを Mathlib `_left/_right` 経由に書き直す mini-refactor に縮退 (Phase 3 で `subsetIdxEquiv` 削除も skip)。それでも Pi.lean は -10 〜 -20 行
- **Phase 2 で `subst hU` が cast を消せない** → Polymatroid 内 2 ヘルパーは現状の subset-form ラッパー経由を維持 (Phase 2 skip)。本 refactor は Pi.lean 内側完結に縮退、合計減 -15 〜 -25 行
- **`MeasurableEquiv.piFinsetUnion` が本 project context (Fintype / DecidableEq / MeasurableSingletonClass 周辺) で発火しない** → これは強烈な驚き。Phase 1 着手最初の 30 分の smoke test で発覚するはず。発覚したら Phase 1 を Pi.lean 内 doc 更新のみに縮退、本 refactor は **見送り** + proof-log に記録

## リスク / 不確実性ランク

| 項目 | 不確実性 | 対処 |
|---|---|---|
| `MeasurableEquiv.coe_piFinsetUnion : rfl` | **低** | Phase 1 最初の 30 分 smoke test |
| `MeasurableEquiv.piFinsetUnion_apply_left/_right` の defeq 透過 | **低-中** | Mathlib `Equiv.piFinsetUnion_left` の `set_option backward.isDefEq.respectTransparency false` から推測すると defeq が脆い場面あり、`MeasurableEquiv.coe_piFinsetUnion` 経由で踏み越える proof を試す |
| `↥(T₁ ∪ (T₂ \ T₁)) → α` ↔ `↥T₂ → α` の cast | **中** | `MeasurableEquiv.cast` が動かなければ `Finset.union_sdiff_of_subset` を `▸` で適用する手筋を試す |
| Polymatroid `jointEntropySubset_submodular` 本体の回帰 | **低** | API 不変なので原理的に回帰しないが、`lake env lean` で逐次確認 |
| Pi.lean docstring の更新漏れで Mathlib `piFinsetUnion` への意図が伝わらない | **低** | Phase 4 の最後に docstring 全部 grep して確認 |

## Definition of Done

1. `InformationTheory/Shannon/Pi.lean` から自前 `subsetIdxEquiv` が **削除済** (Phase 3 完了時)、**かつ** subset 形 `subsetSplitMEquiv` / `subsetSplitMEquiv_apply` も撤去済 (call site 2 ヶ所を `subsetSplitMEquivAux` 直接呼び出しに改修)。Pi.lean の Pi reshape API は `subsetSplitMEquivAux` + 3 本の `MeasurableEquiv.piFinsetUnion_*` bridge に集約。
2. `InformationTheory/Shannon/Pi.lean` に `MeasurableEquiv.coe_piFinsetUnion` + `MeasurableEquiv.piFinsetUnion_apply_left` + `MeasurableEquiv.piFinsetUnion_apply_right` (or 同等の Mathlib bridge) が追加済。
3. `lake env lean` が **3 ファイル全て silent**:
   - `InformationTheory/Shannon/Pi.lean`
   - `InformationTheory/Shannon/HanD.lean`
   - `InformationTheory/Shannon/Polymatroid.lean`
4. `InformationTheory/Shannon/Polymatroid.lean` の `jointEntropySubset_submodular` 本体 proof は **無変更** (回帰なし)。
5. `git diff --stat` で 3 ファイル合計 **-30 〜 -45 行 純減** (撤退ライン適用時は -10 〜 -25 行)。
6. proof-log (`docs/proof-logs/proof-log-hand-pi-refactor.md`) に: Mathlib `piFinsetUnion` の coe / apply 周りで詰まった部分、subst 戦略の defeq 観察、Pi.lean の docstring 設計判断を記録。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-11: subset-form `subsetSplitMEquiv` 撤去 + call site 2 行修正

Phase 1〜4 完了直後、構造的ゴール (Mathlib `MeasurableEquiv.piFinsetUnion` ベース化、
`subsetSplitMEquivAux` 集約、4 ファイル全て silent) は達成したが、行数 Done 条件
(-30 〜 -45) を **未達** (+5 net)。Approach (戦略の shape) §1 で「subset-form ラッパーを
維持して call site 無変更」と書いた前提を見直し、call site 2 行修正を許容する判断に切替。

- **撤去**: Pi.lean から subset 形 `subsetSplitMEquiv` (def 5 行) と
  `subsetSplitMEquiv_apply` (apply lemma 9 行) を削除。
- **call site 改修 (2 ヶ所)**: HanD `condEntropy_subset_anti` と
  Polymatroid `jointEntropySubset_mono` で、`Finset.disjoint_sdiff` +
  `Finset.union_sdiff_of_subset h` を inline で `subsetSplitMEquivAux` /
  `subsetSplitMEquivAux_apply` に渡す形に書き換え。各 site +2〜3 行。
- **結果**: 4 ファイル全 `lake env lean` silent (Pi / HanD / Polymatroid / SlepianWolf)。
  `git diff --numstat` 合計 +102 -114 = **-12 net 行**。当初目標 (-30 〜 -45) には
  届かないが、+5 状態 (撤退ライン) からは 17 行改善。
- **理由**: Approach §1 の「call site 無変更」は cost 評価ミス。call site の
  2 行追加 (Disjoint/union 引数の inline 構築) は subset-form ラッパー全体
  (def + apply lemma + docstring) の維持コストより明確に小さい。Polymatroid
  `jointEntropySubset_disjoint_union` / `condEntropy_reshape_disjoint_union` は
  既に aux 直接呼び出し (Phase 2) のため、subset-form 撤去で `InformationTheory.Shannon.Pi`
  の API 表面が `subsetSplitMEquivAux` 1 本に集約され、上流可読性も向上。
- **DoD #1 / #5 反映**: DoD #1 (`subsetIdxEquiv` 削除) は既に達成 (Phase 3 完了時)。
  本判断で **追加で `subsetSplitMEquiv` (subset 形) も撤去**。DoD #5 の数値目標
  (-30〜-45) は未達だが、aux への一本化という構造改善を優先。Polymatroid
  `jointEntropySubset_submodular` 本体は無変更 (回帰なし)。

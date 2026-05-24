# proof-log: brunn-minkowski-closure Phase V (clean verify + 残存 honest hyp 棚卸し)

session: 2026-05-25
agent: lean-implementer (Wave 3-4)
parent plan: docs/shannon/brunn-minkowski-closure-plan.md (§Phase V, L248-258)

## 検証結果

- `lake env lean Common2026/Shannon/BrunnMinkowskiClosure.lean` (worktree、parent
  `.lake` symlink reuse): **silent** (exit 0、出力 0 行)。
  - error: 0
  - sorry: 0
  - warning: 0
- file 規模: 973 行。
- `Common2026.lean` 編入: 既に済 (Wave 3 で追加済、本 turn 無変更)。

## `:= True` placeholder grep 結果

```
rg -n 'Prop\s*:=\s*True' Common2026/Shannon/BrunnMinkowskiClosure.lean
→ 0 hits
```

honest hyp はすべて実 `Prop` で定義されており、`:True` placeholder による検証回避は
**検出ゼロ**。

## `@audit:` タグ grep 結果

```
372:`@audit:suspect(brunn-minkowski-closure-plan)` -/   ← brunn_minkowski_volume_indicator
492:`@audit:suspect(brunn-minkowski-closure-plan)` -/   ← brunn_minkowski_entropy_jointPi
```

2 件、いずれも plan §Phase V L254/L255 で言及された既知 suspect。語彙
(`docs/audit/audit-tags.md`) 整合済。

## 残存 honest hyp 棚卸し

### 1. `IsSlicePLReadyHyp` (Phase 1 残、regularity bundle)

- def file:line: `Common2026/Shannon/BrunnMinkowskiClosure.lean:228`
- 引用 site (consumer): `prekopa_leindler_nDim` (`:263`) の `h_ready` 引数。
- Prop signature (verbatim):

  ```lean
  def IsSlicePLReadyHyp {n : ℕ}
      (f g hfn : (Fin (n + 1) → ℝ) → ℝ) (lam intF intG intH : ℝ) : Prop :=
    (∀ t : ℝ, 0 < t → IsCompact {s : ℝ | t ≤ sliceInt f s}) ∧
    (∀ t : ℝ, 0 < t → IsCompact {s : ℝ | t ≤ sliceInt g s}) ∧
    (∀ t : ℝ, 0 < t → ({s : ℝ | t ≤ sliceInt f s}).Nonempty) ∧
    (∀ t : ℝ, 0 < t → ({s : ℝ | t ≤ sliceInt g s}).Nonempty) ∧
    (∀ t : ℝ, 0 < t → volume {s : ℝ | t ≤ sliceInt hfn s} ≠ ∞) ∧
    IsPL1LayerCakeIntegralHyp
      (fun t => (volume {s : ℝ | t ≤ sliceInt f s}).toReal)
      (fun t => (volume {s : ℝ | t ≤ sliceInt g s}).toReal)
      (fun t => (volume {s : ℝ | t ≤ sliceInt hfn s}).toReal) intF intG intH ∧
    IsTailIntegrableHyp
      (fun t => (volume {s : ℝ | t ≤ sliceInt f s}).toReal)
      (fun t => (volume {s : ℝ | t ≤ sliceInt g s}).toReal)
      (fun t => (volume {s : ℝ | t ≤ sliceInt hfn s}).toReal)
  ```
- 性質: **regularity bundle** (slice superlevel sets の `IsCompact` / `Nonempty` /
  `≠ ∞` + layer-cake 恒等式 hyp + tail integrability hyp の 7-conjunction)。slice
  1D-PL engine `prekopa_leindler_1D_superlevel_discharged` の解析的前提を bundle
  化したもので、本 file scope 外の measure-theory 配線。
- `:= True` 使用: **否**。すべて実 Prop の連言。
- 判定: **honest** (regularity 寄り、load-bearing ではなく engine の前提条件)。
- discharge 候補: compact-support の indicator 特殊化 (`brunn_minkowski_volume_indicator`
  方向では `A, B` compact 仮定で `IsCompact` / `Nonempty` は供給可、layer-cake +
  tail hyp は §I 以降の indicator readiness 経路で genuine 供給予定)。

### 2. `IsUniformOnEntropyLogVol` 相当 (Phase 3 残、load-bearing 寄り、equality 3 本)

- 形態: **standalone `def` ではなく**、`brunn_minkowski_entropy_jointPi` (L493)
  / `brunn_minkowski_entropy_inequality_genuine` (L531) /
  `brunn_minkowski_entropy_inequality_scaledMul` (L695) の **直接引数** として
  3 本の equality hyp の形で持つ:

  ```lean
  (hA_unif  : Common2026.Shannon.jointDifferentialEntropyPi (P.map X)         = Real.log volA)
  (hB_unif  : Common2026.Shannon.jointDifferentialEntropyPi (P.map Y)         = Real.log volB)
  (hAB_unif : Common2026.Shannon.jointDifferentialEntropyPi
                (P.map (fun ω => X ω + Y ω))                                  = Real.log volAB)
  ```
- 配置 (3 consumer × 同型 3 本):
  - `brunn_minkowski_entropy_jointPi`             at `:499-502`
  - `brunn_minkowski_entropy_inequality_genuine`  at `:538-541`
  - `brunn_minkowski_entropy_inequality_scaledMul` at `:701-704`
- 性質: **load-bearing 寄り** (uniform distribution の entropy = log vol という
  **等式** を仮定として与える。本 plan の主 Mathlib 壁: Jensen 積分形での discharge
  は `MultivariateDiffEntropy.lean` 側 honest hyp bundle と二重化するため pivot、
  別 sub-plan defer。Phase 3 解説 plan L291 と整合)。
- `:= True` 使用: **否**。`= Real.log volA` という具体的 equality (vol > 0 なので
  vacuous truth ではない、`log volA` は well-defined real)。
- 判定: **honest** (具体内容のある equality 仮定、`:= True` でも循環でもない)。
- docstring 明示: `brunn_minkowski_entropy_jointPi` docstring L482-483 で
  「uniform=log-vol hypotheses で各 entropy power を vol^(2/n) に書き換え」と
  load-bearing 役割が明示済。さらに L475 で「🟢ʰ load-bearing hypothesis — NOT
  a discharge」と honest label 付与済。
- discharge 候補: Jensen 積分形 (`Real.concaveOn_negMulLog` + `ConcaveOn.le_map_integral`、
  loogle 確認済) での別 sub-plan、または `MultivariateDiffEntropy.lean` 側
  subadditivity の uniform 特殊化経由。

### 3. `IsBMEntropyPowerVolumeHyp` / `IsBMScaledMulHyp` (Phase 4 残、regularity ↔ geometric BM image)

- def files:lines:
  - `IsBMEntropyPowerVolumeHyp` at `:440`
  - `IsBMScaledMulHyp` at `:577`
- Prop signatures (verbatim):

  ```lean
  /-- sqrt 形 (Cover-Thomas) -/
  def IsBMEntropyPowerVolumeHyp (n : ℕ) (volA volB volAB : ℝ) : Prop :=
    volAB ^ ((1 : ℝ) / n) ≥ volA ^ ((1 : ℝ) / n) + volB ^ ((1 : ℝ) / n)

  /-- scaled multiplicative 形 (より primitive) -/
  def IsBMScaledMulHyp (n : ℕ) (volA volB volAB : ℝ) : Prop :=
    ∀ lam : ℝ, 0 < lam → lam < 1 →
      (lam ^ (-(n : ℝ)) * volA) ^ lam * ((1 - lam) ^ (-(n : ℝ)) * volB) ^ (1 - lam)
        ≤ volAB
  ```
- 性質:
  - sqrt 形 `IsBMEntropyPowerVolumeHyp` は scaledMul 形からの **λ-最適化** で
    genuine に reduction 済 (`bm_scaledMul_to_sqrt`, `:589`)。`brunn_minkowski_entropy_inequality_scaledMul`
    (`:695`) では sqrt 形は consumer 直視から消えて scaledMul 形のみが残る。
  - scaledMul 形 `IsBMScaledMulHyp` は **geometric BM の image**:
    `bm_geom_to_scaledMul` (`:661`) で `volume_smul_nDim` (`:426`) を消費して
    geometric multiplicative BM (`∀ λ, vol(A₁)^λ vol(B₁)^(1-λ) ≤ vol(λ•A₁+(1-λ)•B₁)`、
    `A₁ = λ⁻¹•A`, `B₁ = (1-λ)⁻¹•B`) から genuine に導出可能。よって
    `IsBMScaledMulHyp` は `:= True` 系の vacuous placeholder ではなく、geometric
    content の scalar 投影。
- `:= True` 使用: **否**。sqrt 形は実 `≥` 不等式、scaledMul 形は `∀ λ` 量化付き
  `≤` 不等式。
- 判定: **honest** (regularity 寄り、Mathlib 壁の凸体 Brunn-Minkowski を `volA / volB
  / volAB` の scalar 投影として外出ししたもの。reduction chain `bm_scaledMul_to_sqrt`
  と genuine 接続 `bm_geom_to_scaledMul` で構造的に geometric content と紐付け済)。

## Phase V 完了判定

- [x] `lake env lean Common2026/Shannon/BrunnMinkowskiClosure.lean` silent (0 error
  / 0 sorry / 0 warning) — 本 turn 確認。
- [x] 残存 honest hyp 列挙完了:
  - 1. `IsSlicePLReadyHyp` (Phase 1 残、regularity bundle、`@audit:suspect` 1 件) ×1
  - 2. uniform=log-vol equality 3 本 (Phase 3 残、load-bearing、3 consumer × 3
       hyp = 9 引数 sites、`@audit:suspect` 1 件) ×3 (× 3 consumer)
  - 3. `IsBMEntropyPowerVolumeHyp` (Phase 4 sqrt 形、scaledMul reduction 済) +
       `IsBMScaledMulHyp` (Phase 4 primitive、geometric BM image) ×2
  - 合計: predicate def 4 件 (`IsSlicePLReadyHyp` / `IsBMEntropyPowerVolumeHyp` /
       `IsBMScaledMulHyp` + `MultivariateDiffEntropy` 側依存) + equality hyp 形 3 種
       (uniform=log-vol)。すべて `:= True` 不使用 + すべて honest 判定。
- [ ] 親 `brunn-minkowski-moonshot-plan.md` 末尾の closure plan へのポインタ確認
  — 本 turn scope 外、別 turn (orchestrator) 対応。

## 観察 / 補足

- **defect 検出**: 0 件。`:= True` / 循環 (`:= h`) / load-bearing 偽装 / name
  laundering いずれも検出ゼロ。
- **plan vs 実装の用語ずれ (補足)**: plan §Phase V L255 は「`IsUniformOnEntropyLogVol`
  3 本」と命名された `def` を想定する記述だが、実装は **standalone `def` を持たず**
  3 consumer に **equality hyp として直接 inline** している (`hA_unif/hB_unif/hAB_unif :
  jointDifferentialEntropyPi μ = Real.log vol`)。これは defect ではない (実 Prop
  であり honest)、ただし将来「`IsUniformOnEntropyLogVol` def を持って共有する」
  refactor を行うときに plan 表現と実装が一致するので便利。本 proof-log では
  実装側の形を正として記録。
- **`IsSlicePLReadyHyp` 内 `IsPL1LayerCakeIntegralHyp` / `IsTailIntegrableHyp`**:
  これら 2 件は本 file 外 (おそらく `BrunnMinkowskiLayerCakeBody` / `BrunnMinkowskiPLBody`)
  で def されており、本 turn では verify silent + bundle 連言が型として通っている
  ことのみ確認。各々の honest 性審査は本 Phase V scope 外 (本 plan の対象は
  closure file 内の hyp)。

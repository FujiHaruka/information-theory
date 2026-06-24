# Polymatroid structure 化 — ボトルネック分析

将来 (a) Mathlib mirror style の structure 設計判断補助、(b) 新規ディレクトリ追加時の universe / import 罠の事前検出、の必要性を判断するベースライン記録。

**定量データ**: 本 Track は Track 1 (HanD Pi refactor) と同 session / 同 prompt_id 内のサブエージェント起動として実行されたため、独立した metrics 抽出は不可。同 session 全体の定量は [docs/metrics/hand-pi-refactor.metrics.md](../metrics/hand-pi-refactor.metrics.md) を参照。本ファイルは定性記録に集中する。

## 0. 対象問題と成果物

`docs/moonshot-seeds.md` 「A. 直接 deferred」項目 "Polymatroid structure 化 (Phase D)" の本実装。Mathlib に集合関数版 `Polymatroid` / `Submodular` / `IsSubmodular` が存在しないため、Mathlib `Matroid` style に倣って新規 `structure Polymatroid (ι : Type*) [DecidableEq ι]` を導入し、entropy をその term として登録する。

成果物:

- `InformationTheory/Polymatroid/Basic.lean` (新規、47 行) — `structure Polymatroid` (rank : Finset ι → ℝ + 3 axiom) + `attribute [ext]`
- `InformationTheory/Shannon/Polymatroid.lean` (+19 行) — `noncomputable def entropyPolymatroid : Polymatroid (Fin n)` を append、既存 4 主定理 (`jointEntropySubset_empty` / `_mono` / `_submodular`) で field 充足
- `InformationTheory.lean` (+1 行) — `import InformationTheory.Polymatroid.Basic` 追記
- 2 ファイル `lake env lean` silent、新規証明ゼロ、合計 67 行 (target 60-130 内)

## 1. 問題のキャラクター

新規証明ゼロ、formalism 設計判断のみの structure 化 refactor。Mathlib `Matroid` の API style を mirror する方針が plan 段階で確定し、判断軸は 4 点 ((a) ディレクトリ位置、(b) `class` vs `structure`、(c) `instance` vs `def`、(d) 既存 4 主定理の re-phrase 是非) に集約。すべて plan recommendation 通りに decision、subagent 実装は plan の skeleton をほぼ literal に写経。

過去 proof-log との比較: 数学的アイデア + 補題探索が中心だった Loomis–Whitney ([proof-log-loomis-whitney.md](proof-log-loomis-whitney.md)) や Polymatroid Phase A〜C ([proof-log-polymatroid.md](proof-log-polymatroid.md)) と異なり、本 Track は「formalism 設計 + 罠掘り起こし」のみ。同種の plumbing tightening として Track 1 ([proof-log-hand-pi-refactor.md](proof-log-hand-pi-refactor.md)) と並ぶ。

## 2. 数学的方針

数学なし。設計判断のみ:

- **(a) ディレクトリ位置**: `InformationTheory/Polymatroid/Basic.lean` (新規)。Polymatroid は combinatorial structure であり Shannon 専用ではない。`Shannon/` 配下に置くと Sanov 系 / matroid 系での再利用時に再 import が必要になる。
- **(b) `class` vs `structure`**: `structure`。同 `ι` 上に複数 polymatroid (entropy / matroid rank) が共存可能、`synthInstance` の曖昧性を回避。Mathlib `Matroid` も同流儀。
- **(c) `instance` vs `def`**: `noncomputable def entropyPolymatroid`。同上理由 + entropy は引数 (`μ`, `Xs`, `hXs`) を取るため term-level の `def` が自然。
- **(d) 既存 4 主定理**: 無変更。`entropyPolymatroid` は wrapper、4 主定理は Polymatroid field の充足元として再利用。projection alias (`Polymatroid.rank_le_of_subset` 等) は demand-driven (現状 caller なし → Phase C 不要)。

## 3. Mathlib 補題探索の実録

| 必要だったもの | クエリ | 試行 | 結果 |
|---|---|---|---|
| 集合関数版 `Polymatroid` の存否 | loogle `Polymatroid` | 1 | `unknown identifier` (literal echo) |
| 集合関数版 `Submodular` の存否 | loogle `Submodular` | 1 | `unknown identifier` |
| `IsSubmodular` 型クラス | loogle `IsSubmodular` | 1 | `unknown identifier` |
| Matroid rank 系の submodularity | rg `Matroid.*submodul` Mathlib/ | 1 | `Mathlib/Combinatorics/Matroid/Rank/{Cardinal,ENat}.lean` (`ℕ∞`-valued、entropy `ℝ` と非互換) |

「Mathlib に無かった」もの:

- **集合関数版 `Polymatroid` / `Submodular` / `IsSubmodular`** — 3 query すべて `unknown identifier` の literal echo (typo-distance hit ですらない)。Polymatroid moonshot Phase 0 軸 1 の再確認。Matroid 系の rank function は存在するが `ℕ∞` 値で entropy `ℝ` と型が合わず、相互運用には別レイヤが必要。本 Track の structure はこの空白を埋める性質を持つ → 上流 PR 候補。

## 4. 試行錯誤と後戻り

### 4.1 Universe annotation の罠

**症状**: Plan の skeleton `structure Polymatroid (ι : Type*) [DecidableEq ι] : Type where ...` を literal に写経したら `universe u_1+1 ≰ 1` で reject。

**原因**: `rank : Finset ι → ℝ` は `Finset ι` のレベル (`u_1`) と `ℝ` のレベル (`0`) の max + 1 = `u_1 + 1` に住む。`: Type` (= `Type 0`) で固定すると universe 不一致。

**抜け方**: `: Type` annotation を落とすだけで Lean が自動で正しい universe を推論。

**教訓**: Plan の skeleton で universe annotation を明示するときは「最小限の正しい annotation」を確認すべき。一般には annotation 自体を落とすのが最も安全。Plan の sample skeleton は `: Type` で書かれていたが、これは類書写経で原典確認なしの可能性。Plan ファイルは本 proof-log 執筆時に amend 済 (universe annotation 注意書き追記)。

### 4.2 `Mathlib.Data.Finset.Basic` が `EmptyCollection` を pull しない

**症状**: `rank_empty : rank ∅ = 0` field を書いたら `EmptyCollection (Finset ι)` の typeclass 検索に失敗。

**原因**: `Mathlib.Data.Finset.Basic` には `EmptyCollection (Finset ι)` instance が定義されていない (`Mathlib.Data.Finset.Empty` で初出)。Mathlib のモジュール分割で「Basic」が必ずしも全 foundational instance を含まないという罠。

**抜け方**: `import Mathlib.Data.Finset.Empty` を追加。最終的な import set: `Finset.Empty`, `Finset.Lattice.Basic`, `Order.Monotone.Basic`, `Data.Real.Basic`。

**教訓**: 「Foo.Basic だから foundational 操作はすべてここにある」想定は外れる。新規 file 作成時は最小 import からスタートし、unknown identifier / typeclass synthesis failure を見て段階的に追加するのが安全。Plan で import set を予測列挙していたが半分外れた。

### 4.3 (期待されたトラブル) `Monotone rank` vs `(h : S ⊆ T)` の binder 整合

**症状**: 期待されたトラブルが起きなかった事例。`rank_mono : Monotone rank` field は `Monotone : (α → β) → Prop` で `⦃a b : α⦄ a ≤ b → f a ≤ f b` 形。一方 `jointEntropySubset_mono` は `(h : S ⊆ T) → ...` 形 (`{}` not `⦃⦄`)。

**抜け方**: `fun _ _ h => jointEntropySubset_mono μ Xs hXs h` の 1 行 wrapper で binder 差を吸収。`Finset` の `LE` instance が `⊆` と defeq なため、proof レベルでは完全に一致。Plan で fallback (1-line field 書き換え) を準備していたが発火せず。

**教訓**: 「期待されたトラブルが起きない」ケースも proof-log に残す価値あり。Plan の Risk 表で「中」マークだった項目が実際「低」だった → 将来の同種 plan で risk overestimate の補正材料。`Finset` の `LE` defeq の透過性は強い (今回 + Track 1 の `Disjoint`/`union` cast 周辺で 2 例目)。

## 5. ボトルネックではなかったもの

- **数学的アイデア**: 新規証明ゼロ。
- **既存 4 主定理の再利用**: Track 1 (HanD Pi refactor) で plumbing が clean になっていたため、4 field の充足はすべて 1〜2 行の `fun ... => existing_theorem μ Xs hXs ...` で済んだ。Track 1 の前段整理が直接効いた。
- **`structure` vs `class` 判断**: Mathlib `Matroid` を mirror した plan recommendation でほぼ即決。
- **olean refresh**: `lake build InformationTheory.Polymatroid.Basic` 1 回で downstream (Shannon.Polymatroid) も clean。CLAUDE.md の upstream-edit policy 通り。
- **コンテキスト長**: orchestrator + subagent 委任で圧迫感なし。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたコスト |
|---|---|---|
| 高 | 新規 structure 設計時の Mathlib 類書 mirror 提案 (Matroid → Polymatroid 等) | plan 段階の設計判断 (10〜20 分) |
| 中 | 新規 file 作成時の universe annotation 自動推論 / 警告 (`structure F : Type` を risky として flag) | §4.1 の罠 (1 fix ターン) |
| 中 | 必要 import の段階的補完 (unknown identifier → 候補 import suggestion) | §4.2 の罠 (1 fix ターン) |
| 中 | loogle `unknown identifier (literal echo)` の "Mathlib に無いことの強い signal" 解釈ガイド (rg より discriminating) | inventory 軸 1 確認の高速化 |
| 低 | `Monotone f` field と `(h : a ≤ b) → ...` 形 lemma の binder mismatch 自動 wrapper | §4.3 (1 行) |

## 7. 補足

- 本 Track は Track 1 (HanD Pi refactor) と同 session 内のサブエージェント起動として実行。proof-log は Track 単位で分離、metrics は session 単位なので Track 2 単独抽出は不可 (定量は Track 1 metrics 参照)。
- `attribute [ext] Polymatroid` は plan 通り追加。将来 `Polymatroid.ext` が「rank が等しい 2 polymatroid は等しい」結論として活用される想定。現状 caller なし。
- 採らなかった代替案: `class IsPolymatroidRank (rank : Finset ι → ℝ)` style。`@[simps]` 経由の field accessor 自動生成 + 推論で entropy 自動 lift の利点はあるが、複数 polymatroid 共存 (entropy / matroid rank / Sanov 系) と `synthInstance` 曖昧性の理由で不採用。
- 上流 PR 候補: 集合関数版 `Polymatroid` structure 自体は Mathlib に追加する価値あり。本 project の `InformationTheory/Polymatroid/Basic.lean` を Mathlib `Mathlib.Combinatorics.Polymatroid` として PR 化できる。

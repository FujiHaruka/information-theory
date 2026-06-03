# Shannon Ch.17: Frontier Sweep — Rename + Minkowski Promote

> **Parent**: 親 moonshot 不在 (Ch.17 EPI 周辺の frontier 統合 plan)。関連:
> - [`epi-moonshot-plan.md`](epi-moonshot-plan.md) §Phase D (Gaussian saturation case)
> - [`epi-stam-fisher-epi-integrated-sweep-plan.md`](epi-stam-fisher-epi-integrated-sweep-plan.md) Phase 3.C (rename 延期判断、Phase V closure)
> - [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) (active、Stream 2 で `entropy_power_inequality_gaussian_saturation` を引用)
> - [`brunn-minkowski-from-epi-discharge-plan.md`](brunn-minkowski-from-epi-discharge-plan.md) (将来 consumer 候補、Gaussian additivity を multivariate に持ち上げる route)
> - [`docs/textbook-roadmap.md`](../textbook-roadmap.md) L52 Ch.17 frontier 行

## 進捗

- [ ] Phase 0 — verbatim consumer 確認 + Mathlib 在庫 hint 検証 📋
- [ ] Phase 1 — (A) `entropy_power_inequality_gaussian_saturation` → `entropyPower_gaussian_additivity` rename 📋
- [ ] Phase 2 — (B-inv) CT 17.9 Minkowski determinant inequality の Mathlib 在庫調査 📋 → `chapter-17-minkowski-inventory.md` (Phase 2 で起草)
- [ ] Phase 3 — (B-impl) Minkowski determinant inequality 実装 / 撤退判断 📋
- [ ] Phase 4 — (C) 副次 cleanup (`_exp_form` / `_log_form` 用語整合、任意) 📋
- [ ] Phase V — 全 file 検証 + honesty-auditor + roadmap update 📋

## ゴール / Approach

Cover-Thomas Ch.17 frontier の 3 アイテムを **段階的** に sweep する:

**Approach 全体像**:

1. **(A) rename**: 既存 `@audit:ok` (Tier 1、proof done) declaration の identifier を Ch.17 用語 (`entropyPower_gaussian_additivity`) に整合させる **純 mechanical refactor**。本体 (signature + body) は touch しない。honesty score 不変、識別子変更のみ。
2. **(B) Minkowski promote**: CT 17.9 Minkowski determinant inequality を新規 declaration として登録する。**ただし Mathlib 在庫 hint (Phase 0 + Phase 2 verbatim 確認後) は partial-negative** — `Matrix.det_add` 系は Mathlib 0 件 (det of sum 公式不在) で **絶対壁**、multivariate Gaussian は `multivariateGaussian` (Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:167、Phase 2 inventory で drift 訂正、Phase 0-B の `gaussianMultivariate` typo 由来 false negative) は実在するが `differentialEntropy` / `entropyPower` の multivariate 形は Mathlib 不在で **部分壁**。Phase 2 inventory 結果は 4 軸中 1=POSITIVE / 2=PARTIAL / 3=PARTIAL / 4=PARTIAL で、Phase 3 default は **2 段構え** (Stage A = shared sorry 補題 ~30 行 + `@residual(wall:minkowski-det-posdef)` 撤退で確実 landing、Stage B = `IsHermitian.spectral_theorem` + `det_eq_prod_eigenvalues` + AM-GM 経路で textbook proof attempt ~80-150 行)。
3. **(C) 副次 cleanup**: 任意。`_exp_form` / `_log_form` は Cover-Thomas 翻訳語との照合だけで決まる軽量項目、(A) と一緒の commit に乗せるか判断。

**順序 / 並列可否**:

- (A) は **先行必須**。(B) plan 内で `entropyPower_gaussian_additivity` を新名で参照するため、rename を先に landing しないと plan 自身が古い名前を抱える。
- (B) Phase 2 inventory は (A) と **並列可** (docs-only、Lean file は touch しない、ただし新名で書く前提)。
- (B) Phase 3 実装は (A) 完了後。
- (C) は (A) と同 file 編集なので **(A) と同 commit に bundle 推奨** (任意)。

**撤退ライン**: Mathlib 壁が深い場合、(B) 全体を **scope-out** して `@residual(wall:n-dim-gaussian-minkowski)` (新規 wall 提案) で signature だけ landing する plan-level fallback を Phase 2 verdict 後に発動可。

---

## Phase 0 — verbatim consumer 確認 + Mathlib 在庫 hint 検証 📋

> 実装に着手する前に rename target 27 occurrence + Mathlib 在庫 hint の verbatim 確認。

### 0-A: rename target consumer の verbatim 再 enumeration

前 plan (`epi-stam-fisher-epi-integrated-sweep-plan.md` Phase 3.C verdict 時点、commit `317704b` 直後) の consumer 数は **8 実 call site + 15+ docstring 言及 = 計 23+**。本 sweep 開始時点 (post Phase V closure) で再計算し、差分を本 plan に記録する。

- [ ] **0-A-1**: `rg -nF 'entropy_power_inequality_gaussian_saturation' InformationTheory/ docs/` で全 occurrence 列挙
- [ ] **0-A-2**: 実 call site (`have ... := entropy_power_inequality_gaussian_saturation ...` 形) と docstring 言及 ("see ..." / "経由") を分離してカウント
- [ ] **0-A-3**: 本 plan §Phase 1 「consumer 表」セクションに verbatim 反映

前 plan で記録された **27 件 (InformationTheory 内) + docs 内** の breakdown:

```
InformationTheory/Shannon/EntropyPowerInequality.lean    : 3 件 (def 1 + docstring 2)
InformationTheory/Shannon/EPIStamStep12Body.lean         : 1 件 (docstring)
InformationTheory/Shannon/EPIStamInequalityBody.lean     : 1 件 (docstring)
InformationTheory/Shannon/EPIStamToBridge.lean           : 6 件 (docstring 4 + call 2)
InformationTheory/Shannon/EPIStamDischarge.lean          : 4 件 (docstring 2 + call 2)
InformationTheory/Shannon/EPIStamStep3Body.lean          : 1 件 (docstring)
InformationTheory/Shannon/EPIStamDeBruijnConclusion.lean : 2 件 (docstring 1 + call 1)
InformationTheory/Shannon/EPIL3Integration.lean          : 6 件 (docstring 4 + call 2)
docs/shannon/*.md                                  : 多数 (plan / inventory 文書)
docs/textbook-roadmap.md                           : 1 件
```

**注**: 0-A-1 で出てくる現在値が上記と乖離していたら本 plan の rename 影響範囲を update する。

### 0-B: Minkowski (B) Mathlib 在庫 negative 仮説の verbatim 検証

orchestrator 本会話で確認済の hint:

- `loogle "Matrix.det, _ + _"` → 48 件中 **`Matrix.det_add` 系 0 件** (det of sum を直接扱う公式は不在)。`det_updateRow_add` / `det_one_add_smul` 等は構造が違う。
- `loogle "Matrix.det, Matrix.PosDef"` → **2 件のみ** (`Matrix.PosDef.det_pos`, `Matrix.PosSemidef.posDef_iff_det_ne_zero`)、Minkowski 形 `det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)` 不在。
- `loogle "ProbabilityTheory.gaussianMultivariate"` → **unknown identifier** (multivariate Gaussian 自体が Mathlib 未収録、univariate `gaussianReal` のみ)。**Drift correction 2026-05-28 (Stream B Phase 2 inventory)**: 上記は識別子 typo 由来の false negative。正しい識別子は `multivariateGaussian` で、Mathlib 実在 (`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:167`、12 declarations)。ただし `differentialEntropy` / `entropyPower` の multivariate 形は Mathlib 不在で依然 wall (entropic route で Phase 3 を組む場合に shared sorry 必要)。

Phase 0 step:

- [ ] **0-B-1**: 上記 loogle 3 query を本 sweep 開始時点で再実行 (Mathlib version drift 検知のため)。差分があれば plan を update
- [ ] **0-B-2**: 「Minkowski → Gaussian additivity (univariate) から直接導出可能」は **n=1 退化形のみ** であることを Phase 2 inventory brief に明示 (二重壁: multivariate Gaussian + det Minkowski の両方が Mathlib 不在)

### Done

- 0-A-3: consumer 表 verbatim 確定 + 本 plan §Phase 1 反映
- 0-B-2: Phase 2 inventory brief の負荷見積もりに二重壁を明示

### 撤退ライン

- **L-CH17-0-α**: rename target consumer 数が 30+ に膨張 → Phase 1 の dispatch を `lean-implementer` 1 件 sequential ではなく **段階的 dispatch (file 単位で 8 batch)** に分割。orchestrator merge コスト増を許容
- **L-CH17-0-β**: Mathlib 在庫 hint が positive 方向に変化 (`Matrix.det_add` 系 or `gaussianMultivariate` が Mathlib に追加) → Phase 2 inventory scope を狭め、Phase 3 実装の sorry 数を削減

---

## Phase 1 — (A) Rename `entropy_power_inequality_gaussian_saturation` → `entropyPower_gaussian_additivity` 📋

### 入力

- 既存 declaration: `InformationTheory/Shannon/EntropyPowerInequality.lean:301` (`@audit:ok` Tier 1、body 22 行 genuine、proof done)
- consumer: Phase 0-A-3 で verbatim 確定した表 (~27 件、8 file 横断)

### 段階方針推奨: **一括 search-replace** (alias 経由ではない)

orchestrator の選択肢:

| 方針 | 利点 | 欠点 | 推奨度 |
|---|---|---|---|
| **(i) 一括 search-replace** (本 plan default) | 1 commit で完結、deprecated alias 不要、honesty score 不変、識別子変更のみで意味変化なし | 27 occurrence 同時編集の review コスト | **○** |
| (ii) deprecated alias 経由 (旧名を `@[deprecated] theorem old := new` で残し、consumer は段階的に書換) | consumer の書換を段階分割可、後方互換 | alias 1 件追加 = 永続的な技術的負債、Tier 1 declaration の意味的本体が 2 つ並ぶ違和感、honesty audit 時に `@[deprecated]` の意味確認コスト | △ |

**推奨理由**:

- 本 declaration は **proof done (Tier 1)** で意味的に確定済。識別子 rename は意味を変えない pure refactor。
- Consumer 27 件は **8 file** に分散しているが、各 file 内 occurrence 数は 1-6 件、`rg --files-with-matches` + `sed` (or Edit replace_all) で 1 file あたり 1 turn 以内で完了見込。
- deprecated alias は本 project の他 sweep で導入例なし (`rg '@\[deprecated\]' InformationTheory/Shannon/` で 0 hit を Phase 1 で再確認)。新規導入はプロジェクト規約から逸脱気味。
- Mathlib 等の external 依存者がいないため後方互換義務もない (`InformationTheory` namespace 内自己完結)。

### Phase 1 step

- [ ] **1-1**: Phase 0-A 完了確認、consumer 表 verbatim 反映済
- [ ] **1-2**: `lean-implementer` 1 件 sequential dispatch (worktree 不要、single-file 系列 edit、main 直接編集)
  - dispatch brief 内容:
    - 対象: `EntropyPowerInequality.lean:301` の `theorem entropy_power_inequality_gaussian_saturation` を `entropyPower_gaussian_additivity` にリネーム
    - body / signature / docstring 本文 (rename pending 行 `:295-297` の旧 stale コメント削除を含む) を touch しない (識別子のみ)
    - consumer 8 file (Phase 0-A-3 で確定した list) の全 occurrence を新名に書換
    - docs 内 plan / inventory ファイルは本 Phase の **scope-out** (plan 文書側は後続 Phase または `git grep -- '*.md'` ベースの incidental update に委ねる、本 Phase は Lean code に限定)
    - 検証: `lake env lean InformationTheory/Shannon/EntropyPowerInequality.lean` + 各 consumer file `lake env lean InformationTheory/Shannon/<file>.lean` で 0 errors
    - **継承タグ check** (CLAUDE.md「継承タグの語彙整合 inline check」): rename 後に `rg -n '@audit:|@residual|🟢ʰ' InformationTheory/Shannon/EntropyPowerInequality.lean` で deprecated タグ残置 0 件を確認 (本 declaration は `@audit:ok` の Tier 1 で、本体タグの変動は想定外)
- [ ] **1-3**: rename 後の `@audit:ok` Tier 1 状態を再確認 (honesty 監査は signature/body 不変なので新規起動不要 — CLAUDE.md「Independent honesty audit」起動条件「signature 変更」に該当しない、ただし新規 `@residual` も導入しないため audit 不要)
- [ ] **1-4**: (任意 / Phase 4 と bundle 可) docs side: `docs/shannon/*.md` 内の旧名言及 (~20+ 件) を新名に書換。本体 plan / inventory の closure 状態とは独立な incidental update

### Done

- `lake env lean InformationTheory/Shannon/EntropyPowerInequality.lean` 0 errors
- 全 consumer file (8 件) `lake env lean` 0 errors
- `rg -nF 'entropy_power_inequality_gaussian_saturation' InformationTheory/` → 0 hit
- `rg -nF 'entropyPower_gaussian_additivity' InformationTheory/` → 9+ hit (本体 + consumer)
- `@audit:ok` Tier 1 維持 (honesty 不変)

### 撤退ライン

- **L-CH17-1-α** (alias 維持): 27 occurrence 一括書換中に予期せぬ型 mismatch / olean 不整合多発 → 旧名 `entropy_power_inequality_gaussian_saturation` を `theorem old := new` の 1 行 alias として残し、consumer は段階的に書換 (本 plan default では非推奨だが緊急 fallback)。`@audit:retract-candidate(rename-alias)` を新規 reason vocab として `audit-tags.md` に追加候補
- **L-CH17-1-β** (rename 全体撤回): consumer 数が Phase 0-A-1 verbatim 確認で予想外に 30+ に膨張 → 本 Phase を **保留** + 本 plan §Phase 2 (Minkowski) を先行可能か検討 (Minkowski 側は新名を前提に書くため、rename 撤回時は Minkowski 側を旧名で書く再設計が必要、コスト面で不利)。実質発火しない撤退ライン
- **L-CH17-1-γ** (新規 tier 5 defect 発見): rename 中に rename 対象周辺で循環 / load-bearing hyp 等の defect を発見 → 停止 + orchestrator にフラグ、Phase 1 完了前に独立 audit 起動

---

## Phase 2 — (B-inv) CT 17.9 Minkowski determinant inequality Mathlib 在庫調査 📋

### 目的

Cover-Thomas Theorem 17.9.1 (Minkowski determinant inequality):

> Let `A, B` be `n × n` positive definite matrices. Then `det(A + B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)`.

を InformationTheory で landing するために必要な Mathlib API を **構造化 per-lemma 形式** (CLAUDE.md「Subagent Inventory of Mathlib Lemmas」: file:line / 完全 signature / 型クラス前提 verbatim / 結論形 verbatim) で網羅する。

### 起動方針

- [ ] **2-1**: `mathlib-inventory` subagent 1 件 dispatch (docs-only、worktree 不要)
- [ ] **2-2**: 出力 file = `docs/shannon/chapter-17-minkowski-inventory.md` (新規)

### dispatch brief draft

```
目的: CT 17.9 Minkowski determinant inequality `det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)`
を InformationTheory で landing するための Mathlib API 在庫を per-lemma 形式で網羅する。

出力先: docs/shannon/chapter-17-minkowski-inventory.md

二重壁前提 (verbatim 確認済):
- (i) `Matrix.det_add` 系 ← Mathlib 0 件 (`loogle "Matrix.det, _ + _"` 48 件中該当 0)
- (ii) `gaussianMultivariate` (multivariate Gaussian) ← Mathlib unknown identifier

調査軸:
1. **Matrix.PosDef 系** (Mathlib `LinearAlgebra/Matrix/PosDef.lean`): 加法閉性 `Matrix.PosDef.add`、det 正値性 `Matrix.PosDef.det_pos`、対角化 / 固有値分解 (Hermitian 経路) の現状在庫
2. **det^(1/n) の代数性質**: `Real.rpow (Matrix.det A) (1/n)` の Mathlib 整備状況、`rpow_add_rpow` 系 Minkowski 不等式 (一般化平均) の連結可能性
3. **AM-GM / Hadamard 不等式**: Minkowski の典型証明 (AM-GM + det 同時対角化) で使う Mathlib lemma の在庫
4. **代替 route**: Gaussian additivity (univariate) → multivariate への lift 経路の在庫 (multivariate Gaussian PDF + `differentialEntropy` ベクトル版が必要、両者 Mathlib 不在見込)

ranking:
- POSITIVE (Mathlib に直接使える lemma あり)
- PARTIAL (近い lemma あるが signature 調整必要)
- NEGATIVE (Mathlib 完全不在、shared sorry 補題化必要)
- UNKNOWN (loogle / rg で確認できなかった、追加調査必要)

per-lemma 形式 (CLAUDE.md「Subagent Inventory of Mathlib Lemmas」):
- file:line
- 完全 signature (型クラス [...] verbatim)
- 引数型 (explicit + instance)
- 結論形 verbatim

範囲外:
- 実装は書かない (本 Phase は inventory のみ)
- multivariate Gaussian の Mathlib 立て上げは scope-out (別 plan 候補、本 inventory で言及のみ)

撤退口: 完全 NEGATIVE な軸が確認できたら、本 inventory にその旨記録 + Phase 3 で
`@residual(wall:...)` 撤退ラインの根拠とする (wall 名候補は本 inventory で提案、
正式 register 入りは Phase 3 で判断)。
```

### 想定 verdict (Phase 0-B verbatim 結果ベース)

| 軸 | 想定 ranking | 根拠 |
|---|---|---|
| 1. `Matrix.PosDef` 加法閉性 | **POSITIVE** | `Matrix.PosDef.add` (70 件中存在確認済) |
| 2. `det^(1/n)` 代数性質 | **PARTIAL〜UNKNOWN** | `Real.rpow_add_rpow` 系 Minkowski は存在見込、`Matrix.det` との連結 lemma は要確認 |
| 3. AM-GM / Hadamard 不等式 | **PARTIAL** | `Mathlib.Analysis.MeanInequalities` 系存在見込、ただし det 特化形は要確認 |
| 4. multivariate Gaussian lift | **PARTIAL** (drift 訂正済、Phase 2 inventory) | `multivariateGaussian` 実在 (Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:167)、ただし `differentialEntropy` / `entropyPower` の multivariate 形は不在、entropic route は別 plan が必要 |

### Done

- `docs/shannon/chapter-17-minkowski-inventory.md` 生成、4 軸 ranking + per-lemma 構造化済
- Phase 3 dispatch brief の素材確定 (どの lemma が shared sorry 補題化対象か明示)

### 撤退ライン

- **L-CH17-2-α**: 4 軸すべて NEGATIVE → Phase 3 を **shared sorry 補題 1 件のみの landing** に縮小 (`minkowskiDeterminantInequality : ... := by sorry` + `@residual(wall:minkowski-det-posdef)`)、本格証明は別 plan に委譲
- **L-CH17-2-β**: 軸 2/3 が POSITIVE → Phase 3 で uni-variate Gaussian additivity から **n=1 退化形** + AM-GM 経路で general n も genuine 化を試行 (Cover-Thomas Theorem 17.9 textbook proof 経路)
- **L-CH17-2-γ**: 軸 4 が positive な surprise (Mathlib に multivariate Gaussian PR が landing 済) → 本 plan を再 scoping、`brunn-minkowski-from-epi-discharge-plan` 等の親 plan と統合

---

## Phase 3 — (B-impl) Minkowski determinant inequality 実装 / 撤退判断 📋

### 入力

- Phase 1 完了 (新名 `entropyPower_gaussian_additivity` を参照可能)
- Phase 2 inventory verdict (4 軸 ranking)

### 配置候補

- **(α) 新規 file** `InformationTheory/Shannon/MinkowskiDeterminant.lean` — multivariate Gaussian / matrix 系の新 family を立てる、将来の凸体 BM / 多次元 EPI と接続しやすい
- **(β) 既存 file** `InformationTheory/Shannon/EntropyPowerInequality.lean` 末尾追記 — Gaussian additivity の直接 corollary 位置付け、import 増やさない

**推奨 = (α) 新規 file**: 必要な Matrix.PosDef / Matrix.det / Real.rpow 関連 import が `EntropyPowerInequality.lean` の現 import policy (`gaussianReal` 系) と異なる軸、本 file の scope を Cover-Thomas 17.7 (EPI) + 17.9 (Minkowski det) 二重化すると docstring header の整合が崩れる。新 file 化で Ch.17 family の細分を維持。

### Phase 3 step (Phase 2 verdict 後 fine-tune)

- [ ] **3-1**: Phase 2 inventory 完了確認、Phase 3 配置方針 (α / β) 確定
- [ ] **3-2**: `lean-implementer` 1 件 dispatch、skeleton-driven (CLAUDE.md):
  - 新 file `MinkowskiDeterminant.lean` skeleton: namespace + import + signature + `:= by sorry` + `@residual(<class>:<slug>)`
  - 主 declaration: `theorem minkowskiDeterminantInequality {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hB : B.PosDef) : Real.rpow (Matrix.det (A + B)) (1/(n:ℝ)) ≥ Real.rpow (Matrix.det A) (1/(n:ℝ)) + Real.rpow (Matrix.det B) (1/(n:ℝ))`
  - **n=1 退化形 corollary** (univariate Gaussian additivity の 1×1 matrix 版): Phase 1 で rename した `entropyPower_gaussian_additivity` から直接導出 (det = scalar value、`(det A)^(1/1) = det A` で entropyPower の univariate 形に reduce)
  - n≥2 本体: Phase 2 verdict ベース、POSITIVE / PARTIAL の軸を組み合わせて proof body を埋める、不可なら **sorry + `@residual(wall:minkowski-det-posdef)`** で撤退
- [ ] **3-3**: skeleton type-check (`lake env lean InformationTheory/Shannon/MinkowskiDeterminant.lean`) 0 errors
- [ ] **3-4**: 1 sorry ずつ fill、可能な範囲で proof done、不可なら `@residual` 撤退
- [ ] **3-5**: `InformationTheory.lean` に import 1 行追加
- [ ] **3-6**: 独立 honesty-auditor 起動 (新規 `sorry` + `@residual` 導入があれば必須)

### 新 wall 候補登録 (Phase 3 verdict 後)

Phase 3 で `@residual(wall:minkowski-det-posdef)` を新規使用する場合、`docs/audit/audit-tags.md`「Wall name register」に以下を追記提案:

| Wall name | 意味 | 関連 textbook 節 |
|---|---|---|
| `minkowski-det-posdef` | Minkowski determinant inequality `det(A+B)^(1/n) ≥ det(A)^(1/n) + det(B)^(1/n)` (PosDef matrices) | Ch.17.9 |

または、Phase 2 verdict で multivariate Gaussian lift 軸が壁の主犯と確定したら別名:

| Wall name | 意味 | 関連 textbook 節 |
|---|---|---|
| `n-dim-gaussian-multivariate` | 多次元 Gaussian の entropy 表式 (`multivariateGaussian` 自体は Mathlib 実在: Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:167、ただし `differentialEntropy` / `entropyPower` の multivariate 形は不在) | Ch.17.9 / Ch.9 AWGN multivariate |

正式 register 入りは「shared sorry 補題が 2+ family で再利用」or「1 family 複数 file で参照」trigger で判定 (`audit-tags.md`「提案中 wall」参照)。本 plan 完了時点では **Proposed** 表に追加し、後続 family sweep で promote 判定。

### Done

- `MinkowskiDeterminant.lean` `lake env lean` 0 errors
- `InformationTheory.lean` import 追加済
- 主 declaration が `@audit:ok` (genuine proof done、Phase 2 が POSITIVE 寄り case) **または** `sorry` + `@residual(wall:...)` (negative case で honest 撤退)
- 独立 honesty-auditor PASS (新規 `sorry` 導入時)

### 撤退ライン

- **L-CH17-3-α**: Phase 2 が全 NEGATIVE → 本 Phase を **signature landing のみ** に縮小 (shared sorry 補題 1 件 + `@residual(wall:minkowski-det-posdef)`)。proof body 完成は別 plan に委譲
- **L-CH17-3-β**: n=1 退化形のみ landing 可、n≥2 本体は壁 → 「univariate corollary」として位置付け、`@audit:ok` for n=1 + `sorry` + `@residual` for general n と分離
- **L-CH17-3-γ**: 配置先 (α / β) で予期せぬ import / olean 不整合 → 一時的に (β) 既存 file 末尾追記に降格、後続 PR で別 file 分離

---

## Phase 4 — (C) 副次 cleanup `_exp_form` / `_log_form` 用語整合 📋

### スコープ

- `entropy_power_inequality_exp_form` / `entropy_power_inequality_log_form` (`EntropyPowerInequality.lean:?`, 既存 `@audit:ok`) の identifier が Cover-Thomas Ch.17 翻訳語と整合しているかを照合
- 用語: Cover-Thomas Theorem 17.7.3 では「(17.32) exp form」「(17.31) log form」と表記 (1991 ed.、`docs/Ch17 EPI.pdf` 等を Phase 4 で参照)

### 推奨

- **default = skip** (本 sweep の primary objective ではない、(A) rename 完了で Ch.17 frontier 主目的達成)
- (A) と同 commit に bundle 検討は (A) dispatch agent の判断に委ねる (consumer 数が少ない or 用語整合済なら touch しない)

### Phase 4 step (任意)

- [ ] **4-1**: Cover-Thomas Ch.17.7 PDF を参照 (`docs/Ch17 EPI.pdf` or 翻訳本) で `_exp_form` / `_log_form` の用語照合
- [ ] **4-2**: 改名必要なら Phase 1 と同流儀の一括 search-replace (consumer は少ないはず)、不要なら本 Phase 完了

### Done

- 用語整合 verdict 記録 (skip / rename どちらかを judgment log に明記)

---

## Phase V — 全 file 検証 + honesty-auditor + roadmap update 📋

### 検証

- [ ] **V-1**: 本 sweep で touch した全 file (`EntropyPowerInequality.lean` + Phase 1 consumer 8 file + `MinkowskiDeterminant.lean` (Phase 3 完了時)) を `lake env lean` で個別検証、0 errors
- [ ] **V-2**: `InformationTheory.lean` import 追加箇所確認
- [ ] **V-3**: `rg -nF 'entropy_power_inequality_gaussian_saturation' InformationTheory/` → 0 hit (rename 完遂確認)
- [ ] **V-4**: `rg "@residual" InformationTheory/Shannon/MinkowskiDeterminant.lean` で新規 residual を列挙、Phase 3 で意図したものと一致するか確認

### audit

- [ ] **V-5**: honesty-auditor 1 件 dispatch (Phase 3 で新規 `sorry` + `@residual` 導入があれば必須、無ければ skip 可)
- [ ] **V-6**: verdict OK / questionable / DEFECT で分岐 (CLAUDE.md「Independent honesty audit」)

### roadmap / 親 plan update

- [ ] **V-7**: `docs/textbook-roadmap.md` L52 Ch.17 frontier 行 update:
  - 「`entropy_power_inequality_gaussian_saturation` → リネーム延期 `entropyPower_gaussian_additivity`」を「リネーム完了 ✅」に書換
  - 「CT 17.9 Minkowski determinant inequality **新規 ✅ promote 候補**」を Phase 3 verdict に応じて update (proof done / shared sorry 補題 / signature landing のいずれか)
- [ ] **V-8**: 関連親 plan の進捗ブロック update:
  - `epi-stam-fisher-epi-integrated-sweep-plan.md` Phase 3.C の「rename 延期 default」言及に「→ `chapter-17-frontier-sweep-plan` で完了」reference 追加
  - `brunn-minkowski-from-epi-discharge-plan.md` の Gaussian saturation 参照 (3 件) を新名に書換 (Phase 1 docs side incidental update でカバー可)
- [ ] **V-9**: 本 plan §判断ログに closure entry 追記

### 撤退ライン

- **L-CH17-V-α**: 1 Phase partial closure (例: Phase 1 完了、Phase 3 が wall:minkowski-det-posdef sorry 撤退) → roadmap 行を「rename ✅ / Minkowski 🟡 staged sorry」と分割表記、本 sweep は **partial closure** で commit
- **L-CH17-V-β**: audit DEFECT 発見 → session 中に sorry-based 書換、L-CH17-3-α 相当の撤退に降格
- **L-CH17-V-γ**: roadmap update で Ch.17 frontier 行が 5 行超に膨張 → 上位 index 性を維持するため別 sub-section (例: 「Ch.17 frontier 詳細」サブ節) に逃がす

### Done

- 全 file 検証 PASS
- audit PASS (該当時)
- roadmap + 親 plan update 済
- 判断ログ entry 追記

---

## 全撤退ライン共通規律

各 Phase の撤退ラインは per-Phase 節参照。共通禁止事項:

- `Prop := True` placeholder / 結論型 ≡ 仮説型 `:= h` 循環 / load-bearing hyp 完成詐称 (`*_discharged` 命名等) / 退化定義悪用 (`density_path := 0` 等) を新規導入しない
- Phase 1 rename は signature/body 不変、honesty 不変、識別子のみ変更 — defect 導入機会なし
- Phase 3 Minkowski は壁が深いと判明したら **即 sorry+@residual 撤退**、load-bearing hypothesis (`IsMinkowskiDetHypothesis` 等の predicate に核を抱えさせる撤退) は禁止 (CLAUDE.md「検証の誠実性」)

---

## 想定 dispatch sequence

| Phase | dispatch type | worktree | 想定 turn | 入力 |
|---|---|---|---|---|
| Phase 0 | orchestrator (本 plan 著者) 自前 | - | 1 | rg + loogle verbatim 再確認 |
| Phase 1 | `lean-implementer` 1 件 sequential | 不要 (single agent、main 直接) | 1-2 | Phase 0 consumer 表 + brief |
| Phase 2 | `mathlib-inventory` 1 件 | 不要 (docs-only) | 1 | Phase 2 brief draft (本 plan §Phase 2) |
| Phase 3 | `lean-implementer` 1 件 sequential | 不要 (新 file 1 つ、main 直接) | 1-3 (Phase 2 verdict 次第) | Phase 2 inventory + skeleton draft |
| Phase 4 | (任意) `lean-implementer` 1 件 or Phase 1 と bundle | 不要 | 0-1 | Cover-Thomas PDF 参照 |
| Phase V | orchestrator (検証) + (条件付) `honesty-auditor` 1 件 | 不要 (audit は docs-only) | 1-2 | 全 touched file list + 新規 residual list |

**並列化判断**: Phase 1 (rename) と Phase 2 (inventory) は **並列可** (Phase 1 = Lean code rename / Phase 2 = docs-only inventory、file 所有権独立)。並列 dispatch する場合は CLAUDE.md「Parallel orchestration」boilerplate 適用、ただし Phase 2 は docs-only なので worktree 不要 (CLAUDE.md exception)。

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 起草時点 (2026-05-28) の前提:
- (A) rename 段階方針: 一括 search-replace を default。alias は L-CH17-1-α 緊急 fallback のみ
- (B) Minkowski Mathlib 在庫 hint: NEGATIVE (二重壁 = Matrix.det_add 不在 + gaussianMultivariate 不在)
  → Phase 3 は shared sorry 補題化 + `@residual(wall:minkowski-det-posdef)` 撤退が現実 default
- (C) `_exp_form` / `_log_form` cleanup: default = skip (本 sweep primary 外)
- 新 wall 候補: `minkowski-det-posdef` または `n-dim-gaussian-multivariate` (Phase 2 verdict で確定)
-->

1. **Phase 2 inventory drift 訂正 (2026-05-28、Stream B mathlib-inventory)**: Phase 0-B で「`gaussianMultivariate` 不在」と記録した「二重壁」前提は識別子 typo 由来 false negative と判明 (正名 `multivariateGaussian`、Mathlib 実在)。実際の状態は **絶対壁 1 件 (`Matrix.det_add` 系) + 部分壁 1 件 (`differentialEntropy`/`entropyPower` の multivariate 形不在)**。4 軸 ranking は 1=POSITIVE / 2=PARTIAL / 3=PARTIAL / 4=PARTIAL で、Phase 3 default を「2 段構え (Stage A shared sorry 補題 30 行 + Stage B textbook proof 80-150 行)」に格上げ。Phase 0-B + Phase 2 table + Phase 3 wall 候補 description を本 commit で訂正。`brunn-minkowski-from-epi-discharge-plan` 等の親 plan の同 typo も将来 sweep で訂正検討 (本 plan scope 外)。

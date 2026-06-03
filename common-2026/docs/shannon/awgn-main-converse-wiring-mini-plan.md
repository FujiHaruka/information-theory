# AWGN converse: main wiring (`awgn_converse` body discharge) mini-plan

> **Parent**: [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md) §「Phase C 失敗時 fallback」C-7 項 / 判断ログ #6「後続セッション送り (4)」
>
> **Slug**: `awgn-main-converse-wiring`
>
> **対象 declaration (1 file 1 body 改変 + 1 file consumer ripple)**:
> - `InformationTheory/Shannon/AWGNConverse.lean:59-70` `awgn_converse` body
>   (現状 `sorry` のみ、tag `@residual(plan:awgn-converse-aux-plan)` +
>   `@audit:closed-by-successor(awgn-converse-aux-plan)`)
> - `InformationTheory/Shannon/AWGNMain.lean` の consumer ripple 評価 (現状は
>   `awgn_converse` 未呼出 = ripple 0、後述で verbatim 確定)
>
> **Status (2026-05-27)**: **完了**。M1-M4 全 closure、採用方針 (i) (`AWGNConverse.lean:2` で
> `import InformationTheory.Shannon.AWGNConverseDischarge` を新規追加、逆向き import 不発火)。
> file scope `AWGNConverse.lean` で 0 sorry / 0 @residual = proof done at file scope。
> wall residual 1 件 (`awgnConverseJoint_pair_mi_ne_top`、`@residual(wall:multivariate-mi)`)
> は `AWGNConverseDischarge.lean:405` に集約維持 (新規分散なし)。

## 進捗

- [x] M0 — caller verbatim 確認 + signature 整合判定 (本 plan 内で済、§「signature 整合 verbatim」) ✅
- [x] M1 — `awgn_converse` body skeleton publish (新引数 3 件追加: `h_feasible` / `h_mi_bridge_per_letter` / `hn_pos`、body は `awgn_converse_F3_discharged` 1 行呼出) ✅
- [x] M2 — `AWGNMain.lean` consumer ripple 解消 (現状 0 件確認済、§「consumer ripple 評価」) ✅
- [x] M3 — verify (`lake env lean` 3 file、type-check done 維持、proof done は wall:multivariate-mi 残置 = 単一 sorry 透過状態) ✅
- [x] M4 — `@audit:closed-by-successor` tag 撤去 + `@residual(plan:awgn-converse-aux-plan)` reclassify (`@residual(wall:multivariate-mi)` 透過、shared lemma 経由) ✅

## ゴール / Approach

### Goal (target signature、新引数 3 件追加形)

```lean
-- InformationTheory/Shannon/AWGNConverse.lean:59-70 (改変後)
theorem awgn_converse
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_feasible : IsAwgnConverseFeasible P N h_meas)
    (h_mi_bridge_per_letter :
        ∀ {M n : ℕ} [NeZero M] (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ i : Fin n,
          (perLetterMI h_meas c i).toReal
            = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
              - InformationTheory.Shannon.differentialEntropy
                  (ProbabilityTheory.gaussianReal 0 N))
    {M n : ℕ} (hM : 2 ≤ M) (hn_pos : 0 < n) (c : AwgnCode M n P)
    (Pe : ℝ)
    (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  exact awgn_converse_F3_discharged P hP N hN h_meas h_feasible
    h_mi_bridge_per_letter hM hn_pos c Pe hPe
```

**前後比較** (verbatim diff):
- 追加引数 3 件: `(h_feasible : IsAwgnConverseFeasible …)` /
  `(h_mi_bridge_per_letter : ∀ {M n} [NeZero M] (_hM) c, ∀ i, …)` /
  `(hn_pos : 0 < n)`
- 既存引数 9 件 (`P hP N hN h_meas {M n} hM c Pe hPe`) は順序維持
- 結論 verbatim 維持 (`Real.log M ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ))) + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1)`)
- body は `awgn_converse_F3_discharged` への 1 行 `exact` (薄い wrapper passthrough)

**禁止**:
- bundle predicate `IsAwgnConverseFeasible` 内部 destructure を `awgn_converse` body
  に書く (= wrapper 階層を 1 段崩す、scope creep) — `awgn_converse_F3_discharged` が
  唯一の discharger entry point
- 新規 `*Hypothesis` predicate / load-bearing bundle の追加 (M3 までで全 bundle
  確定済、本 mini-plan は wiring 専門)
- `awgn_converse` signature から既存引数 (`hP`, `hN` 等) を削除する optimization
  (consumer ripple 評価不能になる、現状 caller 0 件でも将来 caller のため維持)

### Approach (overall strategy / shape of solution — 必須 §)

**戦略**: `awgn_converse_F3_discharged` (`AWGNConverseDischarge.lean:1259-1277`) を
**直接呼出**して `awgn_converse` body の `sorry` を埋める。`awgn_converse` signature
に新 hyp 3 件 (`h_feasible` / `h_mi_bridge_per_letter` / `hn_pos`) を pass-through 形
で追加、body は 1 行 `exact` で `_F3_discharged` に委譲。

#### wall lemma `awgnConverseJoint_pair_mi_ne_top` の扱い (直接呼出 vs hyp 外注 判定)

M3 完了状態の `AWGNConverseDischarge.lean` (verbatim Read 済) で `awgnConverseJoint_pair_mi_ne_top`
(line 406-413、private、`@residual(wall:multivariate-mi)`) は **`isAwgnConverseFeasible_discharger`
body 内で 2 件間接伝播**:
- line 425: `awgnConverseJoint_mutualInfo_ne_top` 経由で Fano `hMI_finite` 供給
- line 531: `awgn_dpi` body 内 inline `h_finite` 経由で DPI `mutualInfo_le_of_markov` 供給

両者とも **public-facing signature には現れない** (= private wall lemma が
`_F3_discharged` の body 内で完結消費)。`_F3_discharged` の signature 上には
`@residual(wall:multivariate-mi)` の hyp が無く、wall は body 内透過。

**判定 = wall lemma 直接呼出 (採用)** — body 透過は M3 設計通り、本 mini-plan で
hyp 外注に変更しない。M4 完成時に `awgn_converse` body も同じ pattern で透過、
`AWGNConverse.lean` 上では新規 `@residual(wall:multivariate-mi)` は導入されない
(file 内 0 sorry、wall は `AWGNConverseDischarge.lean:406` 1 件に集約維持)。

**逆判定 (hyp 外注を採用しない理由)**: `awgn_converse` signature に
`(h_mi_finite : ∀ {M n} [NeZero M] c, mutualInfo (awgnConverseJoint h_meas c) ... ≠ ∞)`
等を追加すると、wall を headline signature に持ち上げ = (i) consumer (将来) が
hyp を供給する必要、(ii) `AWGNConverseDischarge.lean` の private wall lemma が
public 化要求、(iii) wall closure plan (M5 = multivariate-MI 解消 plan、未起草)
完成後に signature を再縮約する double migration が必要 — 不合理。

**結論**: wall は `AWGNConverseDischarge.lean` 内 private 集約のまま、`awgn_converse`
は wrapper 1 行で透過。M5 (multivariate-MI wall closure) が完成すれば
`awgnConverseJoint_pair_mi_ne_top` body が 0 sorry 化 = `awgn_converse` も自動的に
proof done (signature 改変なし)。

#### signature 整合 verbatim 確認

`awgn_converse` (sink、`AWGNConverse.lean:59-70`) 既存引数 vs `awgn_converse_F3_discharged`
(source、`AWGNConverseDischarge.lean:1259-1277`) 既存引数:

| 引数 | `awgn_converse` 現状 | `_F3_discharged` 現状 | M4 後の `awgn_converse` |
|---|---|---|---|
| `(P : ℝ)` | ✅ | ✅ | ✅ (位置 1) |
| `(hP : 0 < P)` | ✅ | ✅ | ✅ (位置 2) |
| `(N : ℝ≥0)` | ✅ | ✅ | ✅ (位置 3) |
| `(hN : (N : ℝ) ≠ 0)` | ✅ | ✅ | ✅ (位置 4) |
| `(h_meas : IsAwgnChannelMeasurable N)` | ✅ | ✅ | ✅ (位置 5) |
| `(h_feasible : IsAwgnConverseFeasible P N h_meas)` | ❌ | ✅ | **追加** (位置 6) |
| `(h_mi_bridge_per_letter : ∀ {M n} [NeZero M] (_hM) c, ∀ i, …)` | ❌ | ✅ | **追加** (位置 7) |
| `{M n : ℕ}` | ✅ | ✅ | ✅ (位置 8-9 implicit) |
| `(hM : 2 ≤ M)` | ✅ | ✅ | ✅ (位置 10) |
| `(hn_pos : 0 < n)` | ❌ | ✅ | **追加** (位置 11) |
| `(c : AwgnCode M n P)` | ✅ | ✅ | ✅ (位置 12) |
| `(Pe : ℝ)` | ✅ | ✅ | ✅ (位置 13) |
| `(hPe : Pe = ((1 / M : ℝ) * ∑ m, …))` | ✅ | ✅ | ✅ (位置 14) |
| 結論型 | identical (verbatim 確認済) | identical | 維持 |

`_F3_discharged` 内で `NeZero M` を `haveI : NeZero M := ⟨by omega⟩` で局所導出
(`hM : 2 ≤ M` から、line 1275)。`awgn_converse` body は 1 行 `exact`、引数を
そのまま forward するだけで `NeZero M` の重複導出は `_F3_discharged` 内に閉じる。

#### M3 で confirmed の bundle predicate 構造的不可能性の再現リスク評価

親 plan 判断ログ #6「continuous MI chain rule Real-ENNReal lift の構造的不可能性」
(M3 で結論済) の本 mini-plan での再現性:

- 本 mini-plan は **wiring 専門** — body 内で `mutualInfo` の `.toReal` / ENNReal-lift
  を計算しない (すべて `_F3_discharged` body 内で完結消費)。よって ENNReal-lift
  構造的不可能性は本 mini-plan に伝播しない (= safe)
- `awgn_converse` signature 上で `(perLetterMI h_meas c i).toReal = …`
  (`h_mi_bridge_per_letter`) を **Real 形 hypothesis** として pass-through するのみ —
  bundle predicate destructure / chain rule application は `_F3_discharged` body 内
- 結論として bundle predicate 構造の M4 wiring での再現 = 無 (wrapper 階層 1 段
  挟むことで隔離済)

### 規模見積もり

| Phase | 内容 | 楽観 | 中央 | 悲観 (壁発動) |
|---|---|---:|---:|---:|
| M0 | caller 確認 (本 plan 内、Read のみ) | 0 (Lean) | 0 | 0 |
| M1 | `awgn_converse` body skeleton + 新引数 3 件追加 + 1 行 `exact` | 10 | 20 | 40 |
| M2 | `AWGNMain.lean` consumer ripple (現状 0 件、潜在 ripple 確認のみ) | 5 | 10 | 30 |
| M3 | verify (lake env lean 3 file、tag 解消) | 5 | 10 | 20 |
| M4 | docstring / tag refine (`@residual` reclassify) | 5 | 10 | 20 |
| **合計** | | **~25** | **~50** | **~110** |

中央予測 **~50 行** (本体は body 1 行 `exact`、docstring + 引数列挙が大半)。
姉妹 mini-plan #M3 (`awgn-converse-c5-mi-finite-bridge`、中央 ~120 行) より小規模 —
wiring 専門で証明 logic 一切なし。

### consumer ripple 評価 (verbatim 確認、§「signature 拡張 verbatim」補強)

`rg -n 'awgn_converse[^_]' InformationTheory/` 結果 verbatim 確認 (本起草 turn で実行済):

| 出現箇所 | 種別 | M4 対応 |
|---|---|---|
| `AWGNConverse.lean:34` | docstring 言及 (`/-! ## Converse — awgn_converse … -/`) | 不要 |
| `AWGNConverse.lean:59` | declaration 本体 (改変対象) | M1 で改変 |
| `AWGNF1Discharge.lean:103` | docstring 言及 (移行履歴) | 不要 |
| `AWGNMain.lean:20, 53, 65` | docstring 言及のみ (実 caller でない) | 不要 (docstring 更新は optional) |
| `AWGNConverseDischarge.lean` (10+ 件) | docstring 言及 + `awgn_converse_*_discharged` 命名 (実 caller でない) | 不要 |
| `AWGNF2F3Discharge.lean:27, 44, 234` | docstring 言及 + `awgn_converse_fano_body` 別命名 | 不要 |
| `AWGNAchievabilityDischarge.lean:1592, 1600, 1602` | docstring 言及 (achievability half 説明) | 不要 |

**実 caller 件数 = 0** (すべて docstring 言及 or 別 declaration の命名衝突)。
`awgn_channel_coding_theorem` (`AWGNMain.lean:69-83`) は achievability half のみ
を結論型に持ち、`awgn_achievability` (achievability 側) のみを呼ぶ — `awgn_converse`
は呼ばない。`awgn_capacity_closed_form` (`AWGNMain.lean:97-115`) は
`awgnCapacity_eq` 経由 で sandwich を組み、`awgn_converse` は経由しない。
`awgn_theorem_of_F2F3_hypotheses` (`AWGNF2F3Discharge.lean:247`) は
`IsAwgnConverseHypothesis` 削除済の F-2/F-3 wrapper で `awgn_converse` 直接呼出
無し (predicate 削除と同時に passthrough 切断、2026-05-27 peer migration commit)。

**M2 ripple コスト = 0 件**。M4 完成時、`awgn_converse` の新引数 3 件は consumer 0
件のため migration 不要。`AWGNMain.lean` docstring の F-3 言及 (line 20, 65) は
optional update (informative にとどめる、tier 2 から「discharge wrapper 経由で
proof done 寸前」に表現変更程度)。

### Mathlib 在庫 (本 mini-plan は wiring 中心、Mathlib API 直接依存薄い)

本 mini-plan は **既存 InformationTheory declaration の薄い wrapper 呼出のみ**。
Mathlib 新規依存なし。依存元 verbatim signature:

```lean
-- AWGNConverseDischarge.lean:1259-1277 (verbatim Read 済、M3 完了状態)
theorem awgn_converse_F3_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_feasible : IsAwgnConverseFeasible P N h_meas)
    (h_mi_bridge_per_letter :
        ∀ {M n : ℕ} [NeZero M] (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ i : Fin n,
          (perLetterMI h_meas c i).toReal
            = InformationTheory.Shannon.differentialEntropy (perLetterYLaw h_meas c i)
              - InformationTheory.Shannon.differentialEntropy
                  (ProbabilityTheory.gaussianReal 0 N))
    {M n : ℕ} (hM : 2 ≤ M) (hn_pos : 0 < n) (c : AwgnCode M n P)
    (Pe : ℝ) (hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M,
        (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)) :
    Real.log M
      ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ)))
        + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1) := by
  haveI : NeZero M := ⟨by omega⟩
  exact isAwgnConverseFeasible_discharger P hP N hN h_meas h_feasible
    h_mi_bridge_per_letter hM hn_pos c Pe hPe
```

**imports 追加** (`AWGNConverse.lean`):
- `import InformationTheory.Shannon.AWGNConverseDischarge` — `awgn_converse_F3_discharged`
  + `IsAwgnConverseFeasible` + `perLetterMI` + `perLetterYLaw` (新引数の型に必要)
- 既存 `import InformationTheory.Shannon.AWGN` は維持 (`IsAwgnChannelMeasurable` /
  `awgnChannel` / `AwgnCode` / `Code.errorProbAt`)
- 追加 import 1 件のみ、`AWGNConverseDischarge.lean` 自身が必要な Mathlib import を
  完備しているので `AWGNConverse.lean` 側 Mathlib import 追加不要

**循環依存リスク**: `AWGNConverseDischarge.lean:2` で既に
`import InformationTheory.Shannon.AWGNConverse` (verbatim Read 済) — `AWGNConverse.lean`
側に逆向き import を追加すると **import cycle** 発生。

→ **回避策**: M3 完了済 `_F3_discharged` の依存方向は `AWGNConverseDischarge` →
`AWGNConverse` (discharge は converse stub を必要としない、wrapper signature は
self-contained)。`AWGNConverse.lean:2` の現状 import (verbatim Read line 1):
```lean
import InformationTheory.Shannon.AWGN
```
ここに `import InformationTheory.Shannon.AWGNConverseDischarge` を追加すると、
`AWGNConverseDischarge.lean:2` の逆向き import と循環。

→ **M1 で確実に確認 + 解消方針**:
- 方針 (i) `AWGNConverseDischarge.lean:2` の `import InformationTheory.Shannon.AWGNConverse`
  を削除可能か確認 (現状 `_F3_discharged` body / `isAwgnConverseFeasible_discharger`
  body / 周辺 declaration が `awgn_converse` を呼んでいない or `AWGNConverse.lean`
  declaration を使っていないなら削除安全)
- 方針 (ii) 削除不可なら `awgn_converse` body discharge を `AWGNConverseDischarge.lean`
  内に **新規 wrapper として publish** (例: `awgn_converse_full` のような **名前
  laundering を避けつつ** 一般化 wrapper、ただし `awgn_converse` signature を一方的に
  copy するのは load-bearing と紙一重 — 慎重に判定、§撤退ライン T-MWC-α 参照)

M1 着手前 (skeleton write 前) に方針 (i)(ii) のいずれかを **verbatim Read で 1 度
確定**してから skeleton publish。

## Phase 詳細

### M0 — caller verbatim 確認 + signature 整合判定 (本 plan 内で済) ✅

完了済:
- `awgn_converse` 既存 signature verbatim (`AWGNConverse.lean:59-70`)
- `awgn_converse_F3_discharged` 既存 signature verbatim
  (`AWGNConverseDischarge.lean:1259-1277`)
- consumer ripple = 0 件 (上記 §「consumer ripple 評価」)
- 循環依存 risk 検知 (`AWGNConverseDischarge.lean:2` で `AWGNConverse` を import 済、
  本 mini-plan で `AWGNConverse → AWGNConverseDischarge` 逆向き import 追加で cycle)

### M1 — `awgn_converse` body skeleton publish 📋

scope: `InformationTheory/Shannon/AWGNConverse.lean` のみ改変。

- [ ] M1-α: `AWGNConverseDischarge.lean:2` の `import InformationTheory.Shannon.AWGNConverse`
  を verbatim Read で必要性確認 (`awgn_converse` declaration が `AWGNConverseDischarge`
  内で参照されるかを `rg 'AWGNConverse\.|awgn_converse'` で確認)
- [ ] M1-β (M1-α の結論次第):
  - **方針 (i) 採用** (import 削除可) なら `AWGNConverseDischarge.lean:2` の import 1 行削除
    + `AWGNConverse.lean` に `import InformationTheory.Shannon.AWGNConverseDischarge` 追加
  - **方針 (ii) 採用** (import 削除不可) なら `AWGNConverseDischarge.lean` 末尾に
    `awgn_converse_full` 等の wrapper を publish、`AWGNConverse.lean` 側は変更不要
    で `awgn_converse` body の `sorry` のみ残置 (タグは `@audit:closed-by-successor`
    から `@audit:retract-candidate` に降格、後続 plan で wrapper 統合)
- [ ] M1-γ: 採用方針に従って 1 行 `exact awgn_converse_F3_discharged …` body 書込
- [ ] M1-δ: 新引数 3 件 (`h_feasible` / `h_mi_bridge_per_letter` / `hn_pos`) の追加
  位置を上記 signature 表に従って verbatim 配置
- [ ] M1-ε: docstring 更新 (`@residual` / `@audit:*` reclassify)、§「タグ reclassify」
  参照

**proof-log**: yes (`proof-log-awgn-main-converse-wiring-m1.md`、Phase B-fano /
B-chain 系列を参考に 50-100 行)。

### M2 — `AWGNMain.lean` consumer ripple 解消 📋

scope: ripple **0 件確認済**、本 Phase は実質 docstring 更新のみ。

- [ ] M2-α: `AWGNMain.lean:20, 53, 65` docstring の F-3 言及を update (現状 `sorry +
  @residual` 状態の記述 → `awgn_converse_F3_discharged` 経由 type-check done、
  wall:multivariate-mi 1 件残置の記述に更新)
- [ ] M2-β: optional — `awgn_channel_coding_theorem` の結論型を converse 統合形に
  拡張する pivot 提案 (本 mini-plan scope 外、後続 plan に defer 推奨、判断ログ #1
  で記録)

**proof-log**: no (docstring only)。

### M3 — verify 📋

- [ ] `lake env lean InformationTheory/Shannon/AWGNConverse.lean` clean (0 errors / 0 sorry)
- [ ] `lake env lean InformationTheory/Shannon/AWGNConverseDischarge.lean` clean
  (1 sorry = `awgnConverseJoint_pair_mi_ne_top` 維持、import 改変が body に影響
  しないことを確認)
- [ ] `lake env lean InformationTheory/Shannon/AWGNMain.lean` clean (docstring 更新で
  type-check 影響なし)
- [ ] `rg -n '@residual|@audit:' InformationTheory/Shannon/AWGNConverse.lean` で deprecated
  タグ残置なし確認 (Brief content checklist 2 番、legacy tag 残置 = tier 4 警告)
- [ ] **import cycle 不発火**確認 (M1-α/β の方針 (i)(ii) 採否を verify で逆検証)

**proof-log**: yes (`proof-log-awgn-main-converse-wiring-m3.md`)。

### M4 — `@audit:closed-by-successor` tag 撤去 + reclassify 📋

`AWGNConverse.lean:58` 現状 docstring tag:
```
@audit:closed-by-successor(awgn-converse-aux-plan) @residual(plan:awgn-converse-aux-plan)
```

M4 完成時 (= 本 mini-plan closure 時):

- 方針 (i) 採用 (import 経路解消、body = `awgn_converse_F3_discharged` 1 行
  passthrough、`AWGNConverse.lean` 内 0 sorry):
  → タグ全削除 (`@audit:ok` には届かず — wall:multivariate-mi が body 経由で
  間接残置、`@audit:partial-ok` / `@audit:closed-by-successor(wall-multivariate-mi)`
  程度。`docs/audit/audit-tags.md` 「partial-ok」「closed-by-successor」語彙
  ルール verbatim Read 後、最も適合する tag を選定)
- 方針 (ii) 採用 (wrapper を `AWGNConverseDischarge` 側に publish、`AWGNConverse.lean:59`
  body は `sorry` 残置):
  → `@audit:retract-candidate(awgn-main-converse-wiring-superseded)` +
  `@residual(plan:awgn-main-converse-wiring)` reclassify (本 plan で `awgn_converse`
  を retract、新 wrapper に移行する旨を明示)

採用方針確定後 (M1-β verify 後) に M4 で確定形を docstring に書込。

**proof-log**: no (tag refine only)。

## 撤退ライン

段階的降格:

- **T-MWC-α (中央予測)**: 循環依存 (`AWGNConverseDischarge → AWGNConverse` 既存 +
  `AWGNConverse → AWGNConverseDischarge` 新規追加) 解消で方針 (i) 採用 → 単純
  import flip。コスト = `AWGNConverseDischarge.lean:2` import 1 行削除 + 必要なら
  declaration 局所参照を `@[simp]` / verbatim 名前空間引用に書換 (~5 行)
- **T-MWC-β (中央予測)**: 方針 (i) 採用不可 (`AWGNConverseDischarge` 内に `awgn_converse`
  への意味のある参照あり) → 方針 (ii) wrapper を `AWGNConverseDischarge` 末尾に
  publish (`awgn_converse_full P hP N hN h_meas h_feasible h_mi_bridge_per_letter
  hM hn_pos c Pe hPe := awgn_converse_F3_discharged …` 等)、`AWGNConverse.lean:59`
  は **sorry 残置** で tier 3 `@audit:retract-candidate` reclassify、後続 plan
  (`awgn-converse-retract-stub-plan` 等、未起草) で `AWGNConverse.lean` を削除
- **T-MWC-γ (悲観)**: `awgn_converse` signature 改変に伴う未知の consumer 発見
  (本起草で 0 件と判定したが LSP 検証で発見) → consumer ripple migration を別
  mini-plan 化、本 mini-plan は M1 完了時点で打ち切り、`awgn_converse` は
  signature 拡張なし元状態維持で `@audit:retract-candidate(consumer-ripple-found)`
  reclassify
- **T-MWC-fallback (壁発動)**: `awgn_converse_F3_discharged` 内部で M3 当時想定外の
  Mathlib 壁発見 (= M3 audit verdict と矛盾) → 本 mini-plan を打ち切り、判断ログ #N
  で M3 の壁判定見直しを親 plan に escalate。`awgn_converse` body は `sorry`
  維持で `@residual(wall:<新規 wall slug>)` reclassify

撤退ライン全条件で:
- `IsAwgnConverseFeasible` bundle predicate には触れない (M3 で確定済)
- 新規 `*Hypothesis` predicate / load-bearing bundle の追加禁止
- wall:multivariate-mi 残置は `AWGNConverseDischarge.lean:406` の private lemma に
  集約維持 (新規分散禁止)

## 検証手順

`lake env lean` 3 file (InformationTheory root の追加は不要、既に `InformationTheory.lean:106-110`
に `AWGNConverse` / `AWGNMain` / `AWGNConverseDischarge` 全 3 件 import 済 verbatim
確認):

```bash
lake env lean InformationTheory/Shannon/AWGNConverse.lean
lake env lean InformationTheory/Shannon/AWGNConverseDischarge.lean
lake env lean InformationTheory/Shannon/AWGNMain.lean
```

期待結果:
- `AWGNConverse.lean`: **0 errors / 0 sorry / 0 @residual** (= type-check done +
  proof done at file scope、wall は別 file 残置で本 file は完全 closure)
- `AWGNConverseDischarge.lean`: **0 errors / 1 sorry = wall lemma** (M3 完成状態
  維持、変動なし)
- `AWGNMain.lean`: **0 errors / 0 sorry / 0 @residual** (docstring 更新のみ、
  type-check 影響なし)

**proof done 判定**:
- file scope (`AWGNConverse.lean` 単体) では 0 sorry / 0 @residual = **proof done**
- project scope (transitive wall 含む) では `wall:multivariate-mi` 1 件残置 = **proof
  done ではない** (M5 wall closure plan 起動待ち)
- 独立 auditor が `awgn_converse` の signature honesty を verify すれば
  `@audit:partial-ok` 付与可能 (load-bearing hyp なし、bundle predicate は
  regularity packaging、wall は upstream 集約)

**Brief content checklist (CLAUDE.md「継承タグの語彙整合 inline check」)**: 本
mini-plan は body 復元ワークフローではなく **新規 body 書込** のため deprecated
タグ継承の risk 無し。ただし M1 完了時に
`rg -n '@audit:|@residual|🟢ʰ' InformationTheory/Shannon/AWGNConverse.lean` で deprecated
語彙残置を 1 度確認 (現状 `@audit:closed-by-successor` 1 件 = tier 4 legacy、M4 で
適正 tag に reclassify する対象)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-27 — M1-M4 closure (採用方針 (i))**:
   - 循環依存 check: `AWGNConverseDischarge.lean` 側は `AWGNConverse` を import せず
     (verbatim grep 確認済) → 単純 forward import flip で解消。`AWGNConverse.lean:2`
     に `import InformationTheory.Shannon.AWGNConverseDischarge` 追加で完結、起草時に懸念
     した方針 (ii) (`AWGNConverseDischarge` 末尾に独立 wrapper publish) は不要。
   - verify: 3 file `lake env lean` 0 errors。`AWGNConverse.lean` は file scope
     0 sorry / 0 @residual = **proof done at file scope**。`AWGNConverseDischarge.lean`
     は 1 sorry (line 405 `awgnConverseJoint_pair_mi_ne_top`、`@residual(wall:multivariate-mi)`、
     M3 状態維持)、`AWGNMain.lean` は 0 sorry / 0 @residual。**project scope** では
     wall:multivariate-mi 1 件残置で proof done 未達 (M5 wall closure 待ち)。
   - consumer ripple = 0 件 (起草時 §「consumer ripple 評価」判定通り、変動なし)。
     `AWGNMain.lean` docstring update も済 (line 21-25 / 58 / 70-72)。
   - 採用 tag: `@audit:closed-by-successor(awgn-converse-aux-plan, wall-multivariate-mi)`
     (`audit-tags.md` 「closed-by-successor」語彙準拠)。`@audit:partial-ok` ではなく
     `closed-by-successor` を選んだ理由は body が wall に伝播しているため partial 性が
     明確 (= wrapper 1 段経由で wall lemma が間接消費される構造、`partial-ok` が想定
     する「signature 一部 OK」とは異なり、body 全体が後続 plan/wall 待ち)。

<!-- 起草時点の予期事項:
1. **循環依存方針 (i)/(ii) の判定**: M1-α 完了時に方針確定、判断ログ #1 で記録
2. **`AWGNMain.lean` consumer ripple 0 件の独立 verify**: M3 verify 時に
   `rg` 結果を再確認 (新規 caller 追加が他セッションで発生していないか)
3. **wall reclassify tag の最終形**: M4 で `@audit:partial-ok` / `@audit:closed-by-
   successor(wall-multivariate-mi)` / その他のいずれを採用するか、`audit-tags.md`
   verbatim Read 後に判断ログ #N で記録
-->

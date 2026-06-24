# Proof log — EPI case-1 sum producer (L-Sum-struct)

> Plan: `docs/shannon/epi-case1-sum-producer-plan.md`
> File: `InformationTheory/Shannon/EPICase1SumProducer.lean`
> Session: 2026-06-05

## 採用ルートと breakage 実測

**採用 = 既存 `IsDeBruijnRegularityHyp` を返す形を保ち、`Z_law` を park (L-Sum-struct-park)。**

M1 blast-radius 実測:
- `IsRegularDeBruijnHypV2` consumer = **13 file / 50+ 件** (`rg -c IsRegularDeBruijnHypV2 InformationTheory/`)。
  (b-2) で既存 structure の `Z_law` を general-variance 化すると breakage 大。
- (b-1) 新規 sum-専用 structure は blast radius ゼロだが、**wrapper signature が
  `IsDeBruijnRegularityHyp` を固定で要求** (`EPICase1RatioLimit.lean:1517-1518`) するため、
  producer の返り値型を新 structure に差し替えられない。差し替えるには wrapper 全面改変
  (= ルート (c)) が必要で影響大。

→ どのルートでも「既存 `IsDeBruijnRegularityHyp` を返す」制約から逃れられず、その `reg_at .Z_law`
は unit-hardcode `gaussianReal 0 1` を要求する。

## M1 実機械確認 (核心問題の verbatim 裏取り)

skeleton で structure を `refine { … }` し、`Z_law` goal を `show P.map (fun ω => Z_X ω + Z_Y ω)
= gaussianReal 0 1` で型整合確認 → **`show` が通った** = この型が要求されている。sum noise の真の
law は `gaussianReal 0 2` (本 body で `gaussianReal_add_gaussianReal_of_indepFun` から導出、
`1+1=2`)。`gaussianReal 0 1 ≠ gaussianReal 0 2` なので `Z_law` は **FALSE-as-stated**。これは
予測でなく実機械で裏取り済み (plan の核心問題を確定)。

## 各 field の genuine / park 判定

| field | 判定 | 根拠 |
|---|---|---|
| `density_path` | **genuine** | `convDensityAdd pXS (gaussianPDFReal 0 t.toNNReal)` |
| `reg_at .Z_law` | **PARK** | unit-hardcode `gaussianReal 0 1` vs sum `gaussianReal 0 2`、FALSE-as-stated。`@residual(plan:epi-case1-sum-producer-plan)` |
| `reg_at .density_t` | **genuine** | `convDensityAdd pXS (gaussianPDFReal 0 ⟨t, ht.le⟩)` |
| `reg_at .density_t_eq` | **genuine** | `fun _ _ => rfl` (density_t IS the conv-pin) |
| `reg_at .pX` series (pXS_nn/meas/law/mom) | **genuine** | X/Y producer の pX-series plumbing を `S=X+Y` で再利用 (`hXY_ac`⇒rnDeriv witness、`h_mom_S`⇒pX_mom) |
| top-level `density_t_eq` | **genuine** | `t.toNNReal = ⟨t,ht.le⟩` rw、X/Y producer 同型 |
| `integrable_deriv` bound 部 | **genuine** | PB-2b `fisherInfoOfDensity_convDensityAdd_le` が pXS/g_t に発火 (threaded sum-input regularity 経由)、uniform `C=(1/2)·J(pXS).toReal` bound |
| `integrable_deriv` t-可測性 | **PARK (compound)** | 残1 X/Y producer (`EPICase1RatioLimit.lean:2041`) と同型障害。`@residual(plan:epi-case1-sum-producer-plan,plan:epi-case1-debruijn-producer-plan)` |

## 残1 同型障害の確認結果 (PS-3 検証項目)

sum の `integrable_deriv` bound 部は X/Y 残1 と **同設計で genuine に閉じた** (PB-2b 適用、
variance carrier `t` の unit-W pin)。残る t-可測性 sorry は X/Y 残1 (`:2041`) と
**完全に同型** (`logDeriv (convDensityAdd …)` の lintegral に Mathlib parameter-measurability
lemma 不在)。これは予測通りで、残1 が closure すれば sum も同設計で閉じる → compound `@residual`
で残1 依存を明示。

## integrable_deriv bound 部の genuine 化 (PS-3)

X/Y producer の設計(b) (regular density + `IsBlachmanConvReady` precondition 強化) を sum に
適用し、bound 部を genuine に閉じた。`fisherInfoOfDensity_convDensityAdd_le` は λ=1 specialization
で `J(conv) ≤ J(pXS)` を供給 (不等式核は `convex_fisher_bound_of_ready` @audit:ok)。追加した
precondition `h_fisher_S` / `hreg_pXS` / `hnorm_pXS` / `hready_pXS` は全て regularity
(finite Fisher / regular density / normalization / Integrable-boundedness bundle)。

## structure 改変の有無

**structure 改変なし** (blast radius ゼロ)。既存 `IsDeBruijnRegularityHyp` /
`IsRegularDeBruijnHypV2` を一切触らず、producer 1 file 追加のみ。`Z_law` の型不充足は park で
吸収 (structure surgery は wrapper 固定 / blast radius 大で本 session scope 外と判断)。

## PS-4 wrapper 結線

producer の返り値型は wrapper の `h_reg_sum` slot と verbatim 一致
(`IsDeBruijnRegularityHyp (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P`)。`h_pos_stam` の
sum conv-pin conjunct (`:1541-1544`) は wrapper が**別途受け取る hypothesis** であり producer が
満たす義務ではないので、producer の density 形 (`convDensityAdd pXS g_t`) からの逆制約はない。
最終 `_full` wrapper (PB-6) への注入は downstream task。

## 詰まった点 / proof-log 素材

- `gaussianReal_add_gaussianReal_of_indepFun` は `gaussianReal (0+0) (1+1)` を返す。`0+0=0`
  (`simpa`)、`1+1=2` (`norm_num` on ℝ≥0 → `rw`) を分けて潰す必要があった (1 turn ループ)。
- 設計上の後戻りなし。M1 で「既存 structure を返す制約」が確定した時点で route が一意に決まった
  (新規 structure は wrapper 固定で不可、既存改変は blast radius 大)。

## honesty 上の注記 (auditor 向け)

- 追加 precondition (`hXY_ac` / `h_mom_S` / `h_fisher_S` / `hreg_pXS` / `hnorm_pXS` /
  `hready_pXS`) は **全て regularity** (sum input への Lebesgue 密度 / 有限2次モーメント /
  finite Fisher / regular density / normalization / `IsBlachmanConvReady`)。de Bruijn / Fisher
  単調性の不等式核は一切 bundle しない。`*Hypothesis` predicate に核を抱えさせていない。
- `Z_law` park は load-bearing hyp bundling ではなく、**structure-level unit-hardcode が原因の
  FALSE-as-stated field** を honest に sorry park したもの。signature は producer 形を保つ。
- これは案A (structure 全体一般化、ratio core 偽化) と**別物**: structure を一切触らず、
  微分値 `(1/2)·J` も conv-pin variance も触らない。`Z_law` のみ park。

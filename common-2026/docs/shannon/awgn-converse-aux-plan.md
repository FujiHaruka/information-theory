# AWGN converse aux — F-3 discharge plan (stub)

> **Status**: 未着手 (Tier 3 stub)。実 body は別 session で `lean-planner` agent が起草する。
> **Created**: 2026-05-24 (orphan suspect cleanup, defect-inventory-2026-05-24.md Wave 0)。

## Position

- 対象 predicate / 定理: `Common2026/Shannon/AWGNConverse.lean:92` `theorem awgn_converse`
- 当該 tag: `@audit:suspect(awgn-converse-aux-plan)` (line 91)
- 親 moonshot: [`awgn-moonshot-plan.md`](./awgn-moonshot-plan.md)
- 関連 plan: `awgn-achievability-typicality-plan.md` (achievability 側姉妹)

## Motivation

`awgn_converse` は AWGN 容量定理 converse (Cover-Thomas 9.1.2) の F-3 hypothesis form
で、現在 `h_converseBound_lbh : IsAwgnConverseHypothesis P N h_meas` を load-bearing
hypothesis として受け取り、body は `h_converseBound_lbh hM c Pe hPe` の単純適用。
hypothesis 自身が結論を主張する circular shape (`@audit:defect(circular)` 相当だが
ここでは plan 経由の honest staging を選択し `suspect` 表示)。

bundle 内訳 (AWGNConverse.lean:82–87 docstring より):
- Fano's inequality (`fano_inequality_measure_theoretic`)
- Data processing `I(W; Ŵ) ≤ I(X^n; Y^n)`
- Chain rule `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)` (memoryless channel)
- Per-letter max-entropy `I(X_i; Y_i) ≤ (1/2) log(1+P/N)` (Gaussian Y_i bound)
- Per-letter integrability hypothesis (F-3 撤退ラインの主病巣)

## Scope (将来の起草向けメモ)

- Mathlib 壁 4 分類のうち主分類: (b) 解析 — per-letter integrability + max-entropy
  bound (Gaussian Y_i upper-bound) は continuous SMB / Gaussian Y 分布 (`P + N`)
  との合成。`awgn-mi-bridge-plan` と共通の Gaussian MI 解析を共有する余地あり。
- Tier: 3 (long-term residual; achievability F-1 が先)。

## Open questions

- Per-letter integrability hyp は predicate に押し付けるか genuine discharge を狙うか?
- Gaussian Y bound は `differentialEntropy_gaussianReal` + `(1/2) log(1+P/N)` 算術
  で済むはずだが、`mutualInfoOfChannel` の Mathlib 形 (`KL` form) との整合 bridge が
  必要。これは `awgn-mi-bridge-plan` 側の解析と統合できる可能性が高い。

## Closure criteria

- `awgn_converse` 本体から `h_converseBound_lbh` 引数を削除、bundle 内 5 piece を
  個別 staged hyp or genuine Mathlib 化に分解 (achievability 側 `IsAwgnRandomCodingFeasible`
  と同型の bundle pattern が参考)。
- `@audit:suspect(awgn-converse-aux-plan)` を `@audit:ok` または個別 `@audit:staged(...)`
  に降格。

## TODO

- [ ] `lean-planner` で本 plan の Phase 設計 (起草を依頼する際は親 awgn-moonshot Phase
      ナンバリングに align)

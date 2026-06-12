# Parallel Gaussian L-PG1 closure: regularity-bundle discharge + legacy retraction

**Status**: CLOSED ✅ — `IsParallelGaussianPerCoordRegularity` の 3 field (`bddAbove` / `achiever_mi` / `max_ent`) を honest pieces のみから組む constructor を提供し、hypothesis-minimal headline (`parallel_gaussian_capacity_formula_minimal`) を re-publish。legacy passthrough wrapper 群を bookkeeping tag に移行。

**SoT**: `docs/textbook-roadmap.md` Ch.9 (parallel-gaussian) + `docs/shannon/awgn-facts.md`。詳細履歴は git。frozen slug `L-PG1` はコード側 docstring から参照される (`ParallelGaussian/KKT.lean`、`EntropyPower/Inequality.lean` 他)。

> **Parent**: [`parallel-gaussian-moonshot-plan.md`](parallel-gaussian-moonshot-plan.md) §「撤退ライン discharge 子 plan へのポインタ」L-PG1。

## 要点 (再利用可能)
- route (α) per-coord 分解 + 和 を採用。AWGN family 完成形 + chain-rule MI 加法性 (`mutualInfo_pi_eq_sum`) を最大限再利用し、新規解析を最小化。
- 3 field の bundle を直接攻めず per-field で constructor を組むと honest piece を最小に isolate できる (bundle 直接攻めは 1 補題 ~300 行に膨張)。
- `bddAbove` は global P 上界 (Q-free) で取る。`achiever_mi` は product 入力で `mutualInfo_pi_eq_sum` → per-coord AWGN bridge。`max_ent` は出力 subadditivity 起点 + per-coord max-ent + variance allocation。
- achiever 側 MI 加法性 (旧 `multivariate-mi` 壁) は compProd-of-`Measure.pi` factorization を `Measure.pi_eq` 普遍性で self-build して genuine closure (Mathlib に `Kernel.pi` / `lintegral_pi` 不在を多変量 Tonelli で吸収)。
- water-filling inactive coord (`Q i = 0`、`gaussianReal 0 0 = Dirac`) の trivial fibre 処理に注意。

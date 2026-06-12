# T2-B L-PG0 discharge: Parallel Gaussian kernel measurability

**Status**: CLOSED ✅ — 撤退ライン L-PG0 (parallel kernel measurability `isParallelGaussianKernelMeasurable`) を Mathlib 直接 discharge し、capacity formula を `h_parallel_meas` 引数なし形で re-publish。

**SoT**: `docs/textbook-roadmap.md` Ch.9 (parallel-gaussian) + `docs/shannon/awgn-facts.md`。詳細履歴は git。frozen slug `L-PG0` はコード側 docstring から参照される (`ParallelGaussian/Basic.lean` 他)。

## 要点 (再利用可能)
- 核心の観察: parameter-dependent な `Measure.pi (fun i => gaussianReal (x i) (N i))` を、固定 product Gaussian の shift-map pushforward `(Measure.pi (gaussianReal 0 (N i))).map (fun y i => x i + y i)` に書き直す (`gaussianReal_map_const_add` + `Measure.pi_map_pi`)。
- そうすると AWGN F-1 と全く同じ Giry monad 議論 (`measurable_of_measurable_coe` + curry/uncurry + `measurable_measure_prodMk_left`) が使える。`pi_map_pi` で持ち上げる所だけが non-trivial 拡張点。

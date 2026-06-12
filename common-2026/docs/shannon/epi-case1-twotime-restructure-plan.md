# Shannon EPI: case-1 sum closure two-time object 再構成サブ計画

**Status**: CLOSED ✅ — EPI case-1 sum frontier を two-time object (X を時刻 s、Y を時刻 r で独立摂動) で genuine closure。terminal `entropyPower_add_ge_case1_of_regular_twotime` proof-done + 独立監査 PASS。dead difference subgraph + dead sum producer (Z_law defect carrier) を削除。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-case1-debruijn-producer-plan.md`](epi-case1-debruijn-producer-plan.md) §PB-4 / L-Sum-struct
> **Predecessor (superseded)**: [`epi-case1-debruijn-genvar-struct-plan.md`](epi-case1-debruijn-genvar-struct-plan.md)

## 要点 (再利用可能な proof route / 判断軸)
- **two-time が single-t の variance-2 壁を構造的に回避する核心**: X を時刻 s、Y を時刻 r で独立摂動すると、各 partial が unit-noise の de Bruijn `(1/2)·J` で health になり variance-2 view が発生しない。FII-matched path (`s'=1/J_X`, `r'=1/J_Y`) を選ぶと `R'(t) = J_S·(1/J_X+1/J_Y) − 1` となり、解析入力は single-t と同一の harmonic Stam なのに path geometry の自由度だけで ≤0 が出る。
- **matched path の `e^t` 閉形特徴づけ**: matched path 上では両 component entropy power が `N_i(0)·e^t` で増大 (= `N_X/N_Y` 比一定の level set)。これで 1 次元 object の微分を組むのに ODE 解 (Picard-Lindelöf の Lipschitz-Fisher 壁) を経由せず、逆関数構成 `s(t)=N_X⁻¹(C·e^t)` + `HasDerivAt.of_local_left_inverse` で閉じる。
- **J pin は pointwise-smooth (conv-pin) のみ honest**: `J := fisherInfoOfDensityReal (density_t)` を結論に直接埋込み free 変数を作らない。a.e.-pin だと skeptic が non-smooth representative で `J=0` に落とせる (false-as-framed) ので、`density_t_eq` の `∀ x` pointwise pin を使う。
- **single-t ratio line は genuine `@audit:ok` で削除不可 = user 判断要**: GS-A3' REFUTE は difference 形 sister に局在し ratio 形ではない。two-time terminal は「初の closure」でなく parallel な genuine 証明で、差別化は前提の充足可能性 (two-time は variance-2 view を発生させず Stam supply が defect park に entangle しない)。working 証明の破棄は cleanup でなく戦略判断。

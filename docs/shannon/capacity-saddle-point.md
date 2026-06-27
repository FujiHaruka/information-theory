# Ch.7 強逆: capacity 鞍点 `D(W(a)‖q*) ≤ C` サブ計画 🌙

> **Parent**: [`channel-coding-strong-converse-plan.md`](channel-coding-strong-converse-plan.md) §Phase A

**Status**: R-SC1 行使済 🔄 — 親 plan Phase A の load-bearing core を本 plan に移管。
skeleton commit 済（`StrongConverseAsymptotic.lean`、type-check done、`klDiv_channel_le_capacity` +
gateway atom `mutualInfo_segment_hasDerivAt` の body が `sorry`）。両 decl は
`@residual(plan:capacity-saddle-point)` で本 plan を指す。
**Inventory (SoT, 資産根拠)**: [`channel-coding-strong-converse-asymptotic-inventory.md`](channel-coding-strong-converse-asymptotic-inventory.md) §B（capacity 周辺）。
実体存在（sorryAx / decl 有無 / loogle Found 0）はプローズにキャッシュせず `#print axioms` / loogle / `rg` で都度再導出。

## 進捗

- [x] M0 — 在庫（親 inventory §B を流用、真 Mathlib 壁 0、in-project KKT 自作）✅
- [ ] keystone — 恒等式 `I(p;W).toReal = ∑_x p(x)·klDivPmf (W x) (q_p)` 自作 📋（実装の最初の一手）
- [ ] (ii) gateway atom `mutualInfo_segment_hasDerivAt`（**片側** `HasDerivWithinAt (Set.Ici 0) 0`）📋 **最難**
- [ ] (iii) `IsMaxOn` ⟹ 片側微分 ≤ 0 ⟹ `klDivPmf (W a) q* − C ≤ 0` → `klDiv_channel_le_capacity` closure 📋

## ゴール / Approach

**目標**: 容量達成 input `p`（full-support 出力 `q*`）に対し、各入力記号 `a` で
`D(W(a)‖q*) ≤ capacity W` を **genuine** に証明し、code 側 `klDiv_channel_le_capacity`
（`StrongConverseAsymptotic.lean:54`）の `sorry` を外す。これが親 plan の Wolfowitz 強逆で
Phase B の per-codeword 平均一様上界（`μ[X] ≤ C`）を供給する load-bearing core。

**Approach（解の形）**:

> capacity 達成点 `p` における `I(·;W)` の **方向微分の一次最適条件**（KKT / envelope）で鞍点を出す。
> simplex 上の関数 `f(p') := I(p';W).toReal` は `p` で最大 → 各頂点 `δ_a` 方向の **右側** 方向微分が `≤ 0`。
> segment `p_t := (1−t)·p + t·δ_a` に沿った右微分（gateway atom）が
> `D(W(a)‖q*) − I(p;W)` に等しい（**envelope/Danskin cancellation**: 動く reference
> `q_{p_t} = ∑_x p_t(x) W(x)` の寄与は `∑_b (dq/dt)(b) = 0`（確率正規化）で telescope して消える）。
> よって `D(W(a)‖q*) − I(p;W) ≤ 0`、`I(p;W) = C`（`p` が達成点）で `D(W(a)‖q*) ≤ C`。
>
> **危険は gateway atom 1 点**（動く reference 方向微分）に集中。Mathlib 壁ではなく
> in-project の新規方向微分開発で、`csiszar_*` テンプレート（固定 Q 方向微分）が効く。

**片側で取る理由（two-sided は機械的に偽、判断ログ #1）**: gateway atom は **片側**
`HasDerivWithinAt (Set.Ici 0) 0` であって two-sided `HasDerivAt` ではない。境界達成点
（`p a = 0`）では `t<0` で segment が simplex を出て `p_t a = t < 0` となり、`pmfToMeasure` が
`ENNReal.ofReal` で負座標を `0` にクランプ → 非確率測度化し、`I(p_t;W).toReal` が滑らかな
simplex 汎関数から外れて `t=0` で corner が立つ（左微分 ≠ 右微分）。反例: `α=β=Bool`,
`p=δ_false`, `a=true`。下流の一次最適条件は元々 `𝓝[>] 0` の slope（右側）だけを使う
（`csiszar_first_order_condition`）ので、片側形がちょうど必要十分。

## Phase 詳細

### M0 — 在庫 ✅（compressed）

親 inventory §B（capacity 周辺）+ §C（方向微分テンプレート）が SoT。確定: 真の Mathlib 壁 **0 件**、
本 plan は in-project KKT 自作（~200–350 行、template 有）。資産の実体は loogle/`rg` で都度再導出。

主要 in-project 資産（line は実装時 `rg` で再確認、プローズにキャッシュしない）:
- `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ`（`ChannelCoding/Basic.lean:122`）— `I = H(q_p) − ∑_x p(x) H(W x)`。keystone の近道。
- `csiszar_segment_hasDerivAt`（`CsiszarProjection.lean:299`）— **固定 Q** 方向微分の骨格（gateway atom の写経元、ただし reference 固定）。
- `csiszar_first_order_condition`（`CsiszarProjection.lean:389`）— `IsMinOn` ⟹ 微分符号。(iii) で不等号反転して転用。
- `hasDerivAt_klFun`（CsiszarProjection 内で使用済）+ `HasDerivAt.sum` — 微分組立。
- `exists_capacity_achiever`（`ShannonTheorem.lean:326`）— 達成点 `p` の存在（headline 側で `obtain` 可）。

### keystone — 恒等式 `I(p;W).toReal = ∑_x p(x)·klDivPmf (W x の pmf) (q_p の pmf)` 📋（実装の最初の一手）

**proof-log: yes**（新規 identity の Lean 化を記録）。

- **in-project 不在**（`rg "mutualInfoOfChannel.*klDivPmf"` Found 0、loogle も generic な `klDivPmf` sum form のみ — 本 channel-MI = sum-of-KL-to-output 形は無い）→ **自作必須**。Phase A 本体の前提であり、実装の **最初の一手**。
- 近道: `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ`（`I = H(q_p) − ∑_x p(x) H(W x)`）を経由して `∑_x p(x)·klDivPmf (W x) (q_p)` 形に書き換える（`klDivPmf_eq_log_diff_sum` 系 cross-entropy 展開 + 正規化）。~60 行。
- これが立つと gateway atom の微分対象が `∑_x p(x)·D(W(x)‖q_{p_t})` の形になり、envelope cancellation が `∑_b (dq/dt)(b) = 0` で書ける。

### (ii) gateway atom `mutualInfo_segment_hasDerivAt` 📋 **最難**

**proof-log: yes**（envelope/Danskin cancellation の Lean 化）。

code 側 signature（`StrongConverseAsymptotic.lean:86`、**片側** `HasDerivWithinAt (Set.Ici 0) 0`、verbatim はコード参照）:
`segment p_t := (1−t)·p + t·Pi.single a 1` 上の `t ↦ I(p_t;W).toReal` の `t=0` 右微分
`= klDivPmf (W a) q* − I(p;W).toReal`。

- **新規・最難**: reference `q_{p_t} = ∑_x p_t(x) W(x)` が `p_t` と共に動く（`csiszar_segment_hasDerivAt` は **固定 Q** 専用）。動く reference の寄与は `∑_b (dq/dt)(b) = 0` で telescope して消える＝**envelope cancellation**。これが `HasDerivWithinAt` の形で出るかが本 plan 全体の成否を決める決定的 atom。
- 導出: keystone の `∑_x p_t(x)·D(W(x)‖q_{p_t})` を微分。`dH(q_p)/dt = −∑_b (dq_p/dt)(b)·(log q*(b) + 1) = −∑_b (dq_p/dt)(b)·log q*(b)`（∵ `∑ dq/dt = 0` で `+1` 項が消える）。template `csiszar_segment_hasDerivAt` の固定-Q 骨格に動く reference 補正を載せる。
- gateway-atom-first（既に発火）: この atom を最初に建てて壁公算を反証する。**現状はこの atom が `sorry`**（type-check done で commit 済）。

### (iii) 一次最適条件 → `klDiv_channel_le_capacity` closure 📋

**proof-log: no**（template 転用）。

- `IsMaxOn` ⟹ 右側方向微分 `≤ 0`（`csiszar_first_order_condition` の `IsMinOn`⟹符号を **不等号反転** して転用）→ gateway atom の値 `klDivPmf (W a) q* − I(p;W).toReal ≤ 0` → `I(p;W) = capacity W`（`p` が達成点）で `klDivPmf (W a) q* ≤ capacity W`。~30 行。
- これで code 側 `klDiv_channel_le_capacity` の `sorry` を外し、`@residual(plan:capacity-saddle-point)` を除去 → proof done。

### 退化境界 verify ポイント（着手前に確認、CLAUDE.md「Verbatim 確認」）

- `q*(b)=0` の境界: `klDivPmf` の reference 0 で `klFun` が blow-up → `hq_pos`（full-support 出力）が discharge。前提事故しやすい（親 inventory Key-preconditions box）。
- 達成点が simplex **境界**（ある入力で `p(a)=0`）: 上記 two-sided 偽の核。segment は `t∈[0,1]`（= `Set.Ici 0` の右近傍）で simplex 内に留まる → **片側（右）** 微分 `t=0⁺` で処理。`csiszar_first_order_condition` 同様、internal 仮定不要。
- `I(p;W) = capacity W`: `capacity` の sSup 達成は `hp_max`（`IsMaxOn`）から。`capacity_nonneg` 等で `C ≥ 0` 整合も確認。

## 判断ログ

1. **gateway atom two-sided → 片側 訂正（pmfToMeasure clamp、auditor 検証済）**: 当初 two-sided
   `HasDerivAt … 0` 形で計画していたが機械的に **偽**と判明。境界達成点 `p a = 0` で `t<0` の
   segment が simplex を出て `pmfToMeasure` の `ENNReal.ofReal` 負座標クランプにより非確率測度化、
   `I(p_t;W).toReal` に corner が立つ（反例 `α=β=Bool, p=δ_false, a=true`）。片側
   `HasDerivWithinAt (Set.Ici 0) 0` に訂正（code 側 + honesty-auditor 検証済）。下流の一次最適
   条件は元々右側 slope のみ消費するので片側で必要十分。

2. **R-SC1 退避口は sorry + @residual のみ（R-CSP1）**: gateway atom（envelope cancellation）が
   `HasDerivWithinAt` 形で出せない場合、`mutualInfo_segment_hasDerivAt` / `klDiv_channel_le_capacity`
   の **body のみ** `sorry` + `@residual(plan:capacity-saddle-point)`（= 本 plan）を維持（現状）。
   鞍点を `*Hypothesis` / `IsSaddleClaim` predicate に bundle して headline 前提に積むのは **禁止**
   （load-bearing bundling、CLAUDE.md「検証の誠実性」）。万一 sub-step が真の Mathlib gap（動く
   reference 方向微分が Mathlib 完全不在）と判明したら、hypothesis 化でなく Proposed wall
   `capacity-saddle-directional-derivative` の promote 判定へ（gateway-atom-first で先に反証してから）。

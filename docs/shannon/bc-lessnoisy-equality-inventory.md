# BC less noisy の等号 — M0 在庫

> 親 plan (SoT): [`bc-general-region-plan.md`](bc-general-region-plan.md) §Phase 5「等号」/
> §撤退ライン L-BCO7 / L-BCO8 / §判断ログ 11-(l)(m)(n) / 12 / 17。直前 leg の在庫:
> [`bc-inner-outer-bridge-inventory.md`](bc-inner-outer-bridge-inventory.md) /
> [`bc-phase2-union-inventory.md`](bc-phase2-union-inventory.md)。
> ⚠ **改名**: 本ファイル中の `bc_uv_subset_superposition` は現行名 `bc_lessNoisy_uv_subset_superposition` (親 plan 判断ログ 25)。以下は改名前の履歴記録なので本文は訂正しない。

---

## 結論サマリ

**一行**: Phase 5 の等号に使う API は **既存率 約 85%**、**自作は 7 項目**、**Mathlib の壁は 0 件**。
ただし **plan が次手としている包含 `bcOuterRegionUV W ⊆ martonRegionUnionFS W` は偽**
(Q1 = **(A) 偽**、数値反例あり) なので、**次手そのものを差し替える**必要がある。

### Q1 — plan の次手 `bcOuterRegionUV ⊆ martonRegionUnionFS` は **(A) 偽**

劣化 BSC 対 (`q = 0.1`, `p = 0.25`) の superposition corner `(a, b) = (I(X;Y₁|U), I(U;Y₂))` は
`bcCapacityRegion W ⊆ bcOuterRegionUV W` (機械確認済の `bc_capacity_subset_uv`) により外界に入るが、
**`martonRegionUnion W` には入らない** — 補助アルファベット `(|V₁|,|V₂|)` を `(2,2)` から `(5,5)` まで
動かした数値最適化で、3 制約の最小スラックが一様に `-0.013` 前後 (負) で頭打ちになる。
`martonRegionUnionFS ⊆ martonRegionUnion` なので FS 版でも偽。詳細と表は §Q1。

**位置づけの変更**: L-BCO8 が想定していた閉塞 (型 / 濃度上界) ではなく、**目標命題が偽**。
原因は「`martonRegionUnion` が EGK Thm 8.3 の**共通補助変数 `U₀` を持たない形**」であること
(plan §Phase 2 の ⚠ 正直な限界に既記載)。**時分割の補助への吸収も Marton では効かない**
(`I(V₁;V₂)` が `H(Q)` だけ増える、plan §Phase 2) ので、凸化でも埋まらない。

### Q2 — 代替ルート (superposition 経由) は **可**。3 段とも閉じる見込み

- **(1) 達成側の差し替えは probe で機械確認**。`bc_achievability` の `hdeg` を `hln` に、`:1110`–`:1111`
  を `bc_lessNoisy_infoJoint_ge` に差し替えた版が `lake env lean` **silent** (§Q2-1、probe A)。
  `bc_achievability` の direct consumer は **0 decl / 0 file** (`dep_consumers.sh` 実測) なので
  **署名の一般化はタダ**。推奨は「共通形 `bc_achievability_of_infoJoint_ge` に factor out → 既存
  `bc_achievability` は 1 行、less noisy 版も 1 行」で、証明本体の複製ゼロ。
- **(2) 逆包含の単一文字の数学は閉じる**。凸結合の場合分け (`λ = R₂ / b` と `R₂ ≤ 0`) を
  probe B で機械確認 (`probe_timeshare_split` / `probe_timeshare_degenerate` が compile 通過)。
- **(3) 濃度 (`ℕ` 補助 → `Fintype`) は「有限量子化 + closure 回収」で開く**。裾質量の評価は
  `I(U;Y₂ ∣ U_m) ≤ P(U ≥ m) · log |β₂|` で、必要な部品 (`entropy_le_log_card` /
  `condMutualInfo_compProd_fst_eq_lintegral`) は **すべて in-repo に既存**。Carathéodory 路
  (支持補題) は不要。

**ただしブリーフの見立てのうち 1 点は外れ**: `IsBCLessNoisy` は `∀ (U : Type u) [Fintype U] …` を
量化するので、**外界の `ℕ` 補助にはそのままでは当たらない** (universe + `Fintype` の二重の閉塞、
probe で逐語エラー確認)。less noisy を使うのは量子化**後**の有限 `U_m` に限られる。§Q2-3。

### 推奨する次手 (step 分割と行数見積り)

| step | 内容 | 行数 | 依存 |
|---|---|---|---|
| **S0** | `bc_achievability_of_infoJoint_ge` へ factor out + `bc_achievability` を 1 行化 | ~15 | — |
| **S1** | `bc_lessNoisy_achievability` (新ファイル、`Classes.lean` を import) | ~20 | S0 |
| **S2** | `bcSuperpositionRegionFS` の定義 + `⊆ bcCapacityRegion` (`hW` + `hln`) | ~70 | S1 |
| **S3** | 情報量スロットの同定 3 本 (`bcInfo₁/₂/Joint` ↔ `condMutualInfo/mutualInfo` の `.toReal`) | ~90 | — |
| **S4** | `IsUVChannelLaw` から Markov 鎖 2 本 (`U → X → Y₁` / `V → X → Y₁`) + `ν` の 4 つ組法の同定 | ~140 | — |
| **S5** | 有限量子化 `U_m` + 裾評価 `I(U;Y₂∣U_m) ≤ P(U≥m)·log\|β₂\|` + `a_m ≥ a` | ~160 | S3 |
| **S6** | 時分割の補助への吸収 (`Bool × U_m`) と 2 本の混合等式・不等式 | ~180 | S3 |
| **S7** | 全支持への摂動 (`(1-δ)·law + δ·uniform` の連続性) | ~120 | S6 |
| **S8** | 逆包含 `bcOuterRegionUV ⊆ bcSuperpositionRegionFS` の組み立て + headline 等号 | ~90 | S2–S7 |

合計 **~885 行**。S0–S3 は独立に価値が出る (S3 は more capable でも使う)。**最初に S0–S2 を
切る**のが安い — probe が通っているので写経に近く、それだけで headline 1 本になる。

---

## Q1 内界 union の到達範囲

### 数値実験の設計

判定対象は `martonRegionUnion W` (無制約版) への corner 点の所属。`martonRegionUnionFS` は
その部分集合 (`martonRegionUnionFS_subset_union`、`MartonUnion.lean:88`) なので、
無制約版で偽なら FS 版でも偽。

sim は `/private/tmp/.../scratchpad/marton_reach.py` / `marton_reach2.py`。
**Lean の def からの逐語対応** (CLAUDE.md「小ケースの sim で FALSE を判定するときは先に実 def と
照合する」):

| sim の量 | Lean の def | file:line |
|---|---|---|
| `H(p) = -Σ p log p` (自然対数) | `entropy μ Xs = ∑ x, Real.negMulLog ((μ.map Xs).real {x})` | `Shannon/Bridge.lean:40` |
| `(V₁,V₂) ~ pV → X ~ K → (Y₁,Y₂) ~ W` の 5 つ組 | `martonJointDistribution pV K W` | `Marton/Setup.lean:57` |
| `I1 = H(V₁)+H(Y₁)-H(V₁,Y₁)` | `martonInfo₁` | `Marton/Setup.lean:244` |
| `I2 = H(V₂)+H(Y₂)-H(V₂,Y₂)` | `martonInfo₂` | `Marton/Setup.lean:252` |
| `I12 = H(V₁)+H(V₂)-H(V₁,V₂)` | `martonInfoV₁V₂` | `Marton/Setup.lean:262` |
| `R₁≤I1, R₂≤I2, R₁+R₂≤I1+I2-I12` | `InMartonRegion` (3 field) | `Marton/Basic.lean:40` |
| `a = H(U,X)+H(U,Y₁)-H(U,X,Y₁)-H(U)` | `bcInfo₁` | `Achievability/Setup.lean:111` |
| `b = H(U)+H(Y₂)-H(U,Y₂)` | `bcInfo₂` | `Achievability/Setup.lean:100` |

### sim の適合確認 (閉形式との一致、実測)

| 検査項目 | sim | 閉形式 |
|---|---|---|
| `I(X;Y₁)`, uniform `X`, BSC(0.1) | `0.3680642072` | `ln 2 - h(0.1) = 0.3680642072` |
| `I(V₁;V₂)`, `V₁ = V₂` uniform binary | `0.6931471806` | `ln 2 = 0.6931471806` |
| `a` / `b` at `β = 0.2` | `0.2479739437` / `0.0457005415` | `h(β*q)-h(q)` / `ln 2 - h(β*p)` (同値) |
| `V₁=X, V₂=U` の不足量 at `β = 0.2` | `0.0726544936` | `h(β*q) - h(β) = 0.0726544936` |

5 項目とも 10 桁一致。**ブリーフが手計算で予告した不足量 `h(β*q) - h(β)` は正しい**。

### 結果 (劣化 BSC 対 `q = 0.1`, `p = 0.25`、劣化 BSC `p' = 0.1875`)

`U ~ Bern(1/2)`, `X = U ⊕ Bern(β)` の superposition corner に対する
`min(I1 - a, I2 - b, I1+I2-I12 - (a+b))` の最大値 (単位 nat):

| `β` | `a = I(X;Y₁∣U)` | `b = I(U;Y₂)` | `V₁=X,V₂=U` | `(2,2)` | `(3,3)` | `(4,2)` | `(4,4)` |
|---|---|---|---|---|---|---|---|
| 0.05 | 0.079881 | 0.104978 | −0.206448 | **−0.012975** | −0.012975 | −0.012975 | −0.012975 |
| 0.10 | 0.146311 | 0.082283 | −0.146311 | **−0.016115** | −0.016115 | −0.016115 | −0.016115 |
| 0.20 | 0.247974 | 0.045701 | −0.072654 | **−0.012933** | −0.012933 | −0.012933 | −0.012933 |
| 0.30 | 0.315953 | 0.020136 | −0.030171 | **−0.006730** | −0.006730 | −0.006730 | −0.006730 |
| 0.40 | 0.355209 | 0.005008 | −0.007280 | **−0.001807** | −0.001813 | −0.001820 | −0.001835 |

`(5,5)` まで広げた SLSQP epigraph 版でも `β = 0.05` は `−0.012975` のまま
(最適点 `I1 = 0.109253`, `I2 = 0.092003`, `I12 = 0.029373`、**束縛は `R₂ ≤ I₂` と和制約の両方が同時**)。
`β = 0.15` では `−0.015376`。**アルファベットを増やしても改善しない**。

### 退化境界 2 本 (CLAUDE.md「構造の違う 2 つの退化ケース」)

| 境界 | 予測 | 実測 |
|---|---|---|
| `q → 0` (受信機 1 が無雑音、`Y₁ = X`) | 不足量 `h(β*q)-h(β) → 0` ⟹ スラック 0 | `slack(2,2) = slack(3,3) = -0.000000` ✅ |
| `p = 1/2` (受信機 2 が無用、`b = 0`) | corner は `(a, 0)`、`V₂` 定数で到達 ⟹ スラック 0 | `slack(2,2) = 0.000000` ✅ |

どちらも予測と一致。**偽になるのは内点だけ**で、境界では等号 — 反例が最適化のノイズでないことの傍証。

### closure を跨いだ判定

`martonRegionUnion` は closure なので「探索が届かない」では足りない。スラックが一様に
`≤ -0.0129` ということは、union の任意の点 `(R₁,R₂)` が
`max(b - R₂, (a+b) - (R₁+R₂)) ≥ 0.0129` を満たす ⟹ `‖(R₁,R₂) - (a,b)‖ ≥ 0.0129/√2 > 0`。
**corner 点は union の closure から正の距離**にある。

### 判定と含意

**(A) 偽**。しかも corner 点は `bcCapacityRegion W` に入る (superposition 達成 + closure) ので、
**劣化 BSC 対ですら `martonRegionUnionFS W ⊊ bcCapacityRegion W`**。
つまり L-BCO8 の逆包含は「濃度上界か有限量子化で開く」のではなく **成り立たない**。

⚠ 構造的な理由 (蒸し返し防止): `martonRegionUnion` は EGK Thm 8.3 (private message のみ、
共通補助 `U₀` 無し) の形。superposition を含むのは EGK Thm 8.4 (`U₀` 付き) の方で、`U₀` は
`martonRegion` の署名 (`pV : Measure (V₁ × V₂)`, `K : Kernel (V₁ × V₂) α`) に**入る余地がない**。
`U₀` を足すのは `marton_achievability` (`Marton/Achievability.lean:767`) の符号化定理からの
作り直しで、Phase 5 の射程外。

---

## Q2 代替ルートの評価

### 目標の再掲 (等号の最終形)

```lean
theorem bc_lessNoisy_capacity_eq_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hln : IsBCLessNoisy W) :
    bcCapacityRegion W = bcOuterRegionUV W
```

証明戦略 (擬似 Lean):

```
antisymm
  ├ ⊆ : bc_capacity_subset_uv W                          -- 既存、無条件 (Assembly.lean:839)
  └ ⊇ : intro ν hν p hp                                  -- p ∈ uvRegion ν
        b := (uvInfo₂ ν).toReal ; a := (uvInfoSum₂ ν).toReal - b   -- I(U;Y₂) / I(X;Y₁|U)
        U_m := quantize ν.U m ;  b_m ≥ b - ε_m ;  a_m ≥ a          -- S5
        I(X;Y₁) ≥ I(U_m;Y₁) + a_m ≥ b_m + a_m                      -- hln at U_m + chain rule
        p.1 ≤ (uvInfo₁ ν).toReal = I(V;Y₁) ≤ I(X;Y₁)               -- DPI, S4
        λ := p.2 / b_m ;  U' := Bool × U_m                         -- S6 時分割
        bcInfo₁ pU' K' W = λ a_m + (1-λ) I(X;Y₁) ; bcInfo₂ pU' K' W ≥ λ b_m
        bc_lessNoisy_achievability (S1) at (p.1-δ, p.2-δ) → closure
```

### Q2-1 達成側 (probe A) — **機械確認 PASS**

`scratchpad/ProbeLessNoisyAchiev.lean` に `bc_achievability`
(`Achievability/Assembly.lean:1093`) の署名を `hdeg : IsBCDegraded W` →
`hln : IsBCLessNoisy W` に替え、本体は `:1108`–`:1229` の**逐語コピー**、ただし
`bc_degraded_infoJoint_ge pU K W hdeg` → `bc_lessNoisy_infoJoint_ge pU K W hln`
(`:1110`–`:1111`) の 1 箇所のみを変更。`lake env lean` **silent (21 s)**。
⟹ **degradedness は `bc_achievability` の他の場所で効いていない**
(`rg 'hdeg'` の実測も `:1099` (束縛) / `:1111` (使用) の 2 箇所のみ)。

**universe の副作用が 1 点**: `IsBCLessNoisy` が `∀ (U : Type u)` を量化し `α : Type u` なので、
less noisy 版は `U` と `α` を**同一 universe に固定**する必要がある
(`bc_achievability` は `{U α β₁ β₂ : Type*}` = 4 universe)。probe はこの形で通した。
`bcAuxAlphabet` (`MartonUnion.lean:52` = `ULift.{u} (Fin (k+1))`) が Phase 2 で同じ問題を
吸収済なので、union を取る段では追加コストなし。

**推奨する実装形 (複製ゼロ)**: `bc_achievability` の direct consumer は
**0 decl / 0 file** (`scripts/dep_consumers.sh` 実測)、`bc_degraded_infoJoint_ge` は
**1 decl / 1 file** (`Assembly.lean:1080` = `bc_achievability` 自身)、
`bc_lessNoisy_infoJoint_ge` は **0 decl / 0 file**。⟹ 波及ゼロなので

```lean
-- Achievability/Assembly.lean : 現 bc_achievability の本体をこちらへ (hdeg → hsum)
theorem bc_achievability_of_infoJoint_ge … (hsum : bcInfo₁ pU K W + bcInfo₂ pU K W ≤ bcInfoJoint pU K W) …
-- 既存 headline は 1 行に
theorem bc_achievability … (hdeg : IsBCDegraded W) … :=
  bc_achievability_of_infoJoint_ge … (bc_degraded_infoJoint_ge pU K W hdeg) …
-- 新ファイル (Classes.lean を import) で
theorem bc_lessNoisy_achievability … (hln : IsBCLessNoisy W) … :=
  bc_achievability_of_infoJoint_ge … (bc_lessNoisy_infoJoint_ge pU K W hln) …
```

**honesty の自己チェック**: `hsum` は「等号が成り立つ」型の述語ではなく、in-tree の 3 つの def
の間の不等式で、**sorry-free な `@[entry_point]` 2 本 (`bc_degraded_infoJoint_ge` /
`bc_lessNoisy_infoJoint_ge`) が両方向から discharge する**。公開 headline 2 本がどちらも
クラス条件だけを受ける形になるので、条件が残る宣言は生まれない。
`*Hypothesis` 述語への束ねではない (CLAUDE.md tier 5 の load-bearing hyp に当たらない)。
⟹ それでも監査が渋る場合の退避は「本体を複製して 2 本立てる (~120 行の重複)」。

### Q2-2 逆包含の凸結合 (probe B) — **機械確認 PASS**

`scratchpad/ProbeConverseChain.lean` (compile 通過、警告のみ)。

```lean
theorem probe_timeshare_split
    {R₁ R₂ Iv Ix a b : ℝ}
    (hb : 0 < b) (hR₂pos : 0 < R₂)
    (hcorner₁ : R₁ ≤ Iv) (hIvIx : Iv ≤ Ix)
    (hcorner₂ : R₂ ≤ b) (hsum : R₁ + R₂ ≤ a + b)
    (hIx : a + b ≤ Ix) :
    R₂ ≤ (R₂ / b) * b ∧ R₁ ≤ (R₂ / b) * a + (1 - R₂ / b) * Ix
```

と `probe_timeshare_degenerate` (`R₂ ≤ 0` の分岐) が両方通る。
⟹ **ブリーフの `λ = R₂/b` の場合分けは正しい**。`nlinarith` 2 発で閉じる (各 6 行)。

さらに `bcInfoJoint = (mutualInfo _ (U,X) Y₁).toReal` の同定も probe 済:

```lean
theorem probe_bcInfoJoint_eq_mutualInfo_toReal … :
    bcInfoJoint pU K W
      = (mutualInfo (bcJointDistribution pU K W)
          (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) (fun q ↦ q.2.2.1)).toReal
```

**注意点 (実測で判明)**: `MAC.mutualInfo_toReal_eq_entropy_form` が返す 3 項目は
`entropy … (fun ω ↦ ((ω.1, ω.2.1), ω.2.2.1))` (入れ子) なのに `bcInfoJoint` の第 3 項は
`entropy … (fun q ↦ (q.1, q.2.1, q.2.2.1))` (平坦) で、**`rfl` では閉じない**。
単射再ラベルによるエントロピー不変性が 1 本要る (probe では 22 行で自作)。
**同型の補題が in-repo に既存**: `wz_entropy_map_injective`
(`WynerZiv/Achievability/Covering.lean:1189`) — ただし WynerZiv 配下なので BC 側からは
import できない。**S3 で `Shannon/Entropy.lean` へ一般形を上げるのが筋** (「既に書いたか」の
重複を 1 件潰せる)。

### Q2-3 濃度 (`ℕ` 補助) — ブリーフの見立てを 1 点訂正した上で **開く**

**訂正**: 「`ν` の補助は `ℕ`、`bc_achievability` は `[Fintype U]` を要求する」は正しいが、
**先に当たるのは `IsBCLessNoisy` の方**。逐語エラー (probe、コメントアウトで保存):

```
Application type mismatch: The argument
  ℕ
has type
  Type
of sort `Type 1` but is expected to have type
  Type u
of sort `Type (u + 1)` in the application
  @hln ℕ
```

`ULift.{u} ℕ` に上げても `[Fintype]` が出ないので二重に塞がる。
⟹ **less noisy は量子化後の有限 `U_m` にしか当てられない**。ルート設計上は問題ない
(量子化は元々必要) が、「先に `hln` を当てて `I(U;Y₁) ≥ I(U;Y₂)` を取ってから量子化する」
順序では書けない。**量子化 → less noisy** の順に固定すること。

**量子化の数学 (ブリーフの (3) を検算)**:

- `U_m := fun u ↦ if u < m then u else m` (`ℕ → Fin (m+1)`)。`U_m` は `U` の関数。
- `a_m := I(X;Y₁ ∣ U_m) ≥ a := I(X;Y₁ ∣ U)` — **増える**。
  理由: `I(X,U;Y₁ ∣ U_m) = I(U;Y₁∣U_m) + I(X;Y₁∣U,U_m) = I(U;Y₁∣U_m) + a`
  かつ `= a_m + I(U;Y₁∣X,U_m)`、`U → X → Y₁` から後者は 0。
  ⟹ `a_m = a + I(U;Y₁∣U_m) ≥ a` ✅ (ブリーフの予測どおり)
- `b_m := I(U_m;Y₂) ≤ b := I(U;Y₂)` — **減る**。減少量は `b - b_m = I(U;Y₂∣U_m)` (連鎖律)。
- **裾評価**: `U_m = s` (`s < m`) は `U = s` を決めるので `I(U;Y₂∣U_m=s) = 0`。
  `s = m` (裾) では `I(U;Y₂∣U_m=m) ≤ H(Y₂∣U_m=m) ≤ log |β₂|`。
  ⟹ `b - b_m ≤ P(U ≥ m) · log |β₂| =: ε_m → 0` ✅ (ブリーフの「`≤ ε·log|β₂|` 型」は正しい)
- ⟹ `a_m + b_m ≥ a + b - ε_m` と `b_m ≥ b - ε_m` の 2 本があれば
  `{R₂ ≤ b - ε_m, R₁+R₂ ≤ a+b-ε_m}` が時分割で被覆でき、`closure` で `ε_m → 0` を回収。
  **条件付き less noisy (`I(U;Y₁∣T) ≥ I(U;Y₂∣T)`) は要らない** — ε 版で足りるので、
  「クラス条件を条件付き版へ拡張する」補題を書かずに済む。

Carathéodory 型の支持補題 (L-BCO8 の (i)) は **不要**。Mathlib に Carathéodory 本体はあるが
(`Mathlib/Analysis/Convex/Caratheodory.lean:148` `convexHull_eq_union` /
`:161` `eq_pos_convex_span_of_mem_convexHull`)、Fenchel–Eggleston (連結集合版) は
**Mathlib に無い** (`rg 'Eggleston' .lake/packages/mathlib/Mathlib/` が 0 件) ので、
支持補題路を選ぶと自作行数が跳ねる。**量子化路を採ること**。

---

## Q3 資産表

### A. 達成側 (superposition) — 既存

| 概念 | 宣言 (逐語署名の要点、`[...]` 込み) | file:line | 状態 |
|---|---|---|---|
| 劣化 BC 達成側 | `theorem bc_achievability (pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a}) (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hdeg : IsBCDegraded W) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (_hR₂ : 0 < R₂) (hR₁lt : R₁ < bcInfo₁ pU K W) (hR₂lt : R₂ < bcInfo₂ pU K W) {ε' : ℝ} (hε' : 0 < ε')` 結論 `∃ N : ℕ, ∀ n, N ≤ n → ∃ (M₁ M₂ : ℕ) (_hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁) (_hM₂ : …) (c : BroadcastCode M₁ M₂ n α β₁ β₂), (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε'`。変数束は `[Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]` × 4 型 | `Achievability/Assembly.lean:1093` | ✅ 既存 (S0 で `hsum` 版へ factor out) |
| less noisy の和不等式 | `theorem bc_lessNoisy_infoJoint_ge {U : Type u} [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U] (pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hln : IsBCLessNoisy W) : bcInfo₁ pU K W + bcInfo₂ pU K W ≤ bcInfoJoint pU K W` | `Classes.lean:95` (`@[entry_point]`) | ✅ 既存 0 sorry |
| less noisy クラス | `def IsBCLessNoisy (W : BCChannel α β₁ β₂) : Prop := ∀ (U : Type u) [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U] (pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K], mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.2) ≤ mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.1)` | `Classes.lean:63` | ✅ 既存。**`Type u` 量化が `ℕ` を弾く** |
| 3 情報スロット | `bcInfo₂` (`= I(U;Y₂)`, 3 entropy) / `bcInfo₁` (`= I(X;Y₁∣U)`, 4 entropy) / `bcInfoJoint` (`= I((U,X);Y₁)`, 3 entropy)、いずれも `: ℝ` | `Achievability/Setup.lean:100` / `:111` / `ErrorAnalysis.lean:929` | ✅ 既存 |

### B. 操作的領域と closure の帳簿 — 既存

| 概念 | 宣言 | file:line | 状態 |
|---|---|---|---|
| 達成可能性述語 | `def BCAchievable (W : BCChannel α β₁ β₂) (R₁ R₂ : ℝ) : Prop` | `Operational.lean:53` | ✅ |
| 容量領域 | `def bcCapacityRegion (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) := closure {p | BCAchievable W p.1 p.2}` | `Operational.lean:68` | ✅ |
| 下方単調 | `theorem bc_achievable_mono {W} {R₁ R₂ R₁' R₂' : ℝ} (h : BCAchievable W R₁ R₂) (h₁ : R₁' ≤ R₁) (h₂ : R₂' ≤ R₂) : BCAchievable W R₁' R₂'` | `Operational.lean:71` | ✅ |
| 厳密下方からの closure 回収 | `theorem bc_mem_closure_of_strictly_below (W) (p : ℝ × ℝ) (h : ∀ ε : ℝ, 0 < ε → BCAchievable W (p.1 - ε) (p.2 - ε)) : p ∈ closure {q | BCAchievable W q.1 q.2}` | `Operational.lean:86` | ✅ **S2 の主役** |
| 非正レートの clamp | `lemma bc_achievable_clamp_iff (W) (R₁ R₂ : ℝ) : BCAchievable W R₁ R₂ ↔ BCAchievable W (max R₁ 0) (max R₂ 0)` | `OuterBoundUV/Assembly.lean:670` | ✅ **`bc_achievability` の `0 < R` 要求を退化点で迂回する唯一の道** |
| 容量領域は閉 | `theorem bc_capacityRegion_isClosed (W) : IsClosed (bcCapacityRegion W)` | `Operational.lean:102` | ✅ |
| 外界への包含 | `theorem bc_capacity_subset_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W] : bcCapacityRegion W ⊆ bcOuterRegionUV W` | `OuterBoundUV/Assembly.lean:839` (`@[entry_point]`) | ✅ **無条件**。等号の片側は完了済 |

**退化レート `(0,0)` の達成 (S2 の穴埋め)**: `bc_achievability` は `0 < R₁`, `0 < R₂` を要求するが
`bcSuperpositionRegionFS` には符号制約がない (判断ログ 1)。埋め方は
`martonRegion` の**単集合補助**版 (`martonInfo₁ = martonInfo₂ = martonInfoV₁V₂ = 0`、
`martonInfo₁_eq_zero_of_subsingleton` が `Marton/Setup.lean:278`) から
`bc_strict_interior_achievable` (`Operational.lean:131`) で `BCAchievable W (-ε) (-ε)` を取り、
`bc_achievable_clamp_iff` (`max (-ε) 0 = 0`) で `BCAchievable W 0 0` に落とす。~15 行。
**新規の符号化定理は要らない** (`rg` 実測で `BCAchievable W 0 0` 系の既存補題は 0 件)。

### C. 外界側 (`ν` の取り扱い) — 既存

| 概念 | 宣言 | file:line | 状態 |
|---|---|---|---|
| チャネル法の制約 | `def IsUVChannelLaw (W : BCChannel α β₁ β₂) (ν : Measure (U × V × α × β₁ × β₂)) : Prop := ν.map (fun q ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) = (ν.map fun q ↦ (q.1, q.2.1, q.2.2.1)) ⊗ₘ W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)`。`[MeasurableSpace U] [MeasurableSpace V]` のみ | `OuterBoundUV/Region.lean:104` | ✅ |
| 特徴づけ | `lemma isUVChannelLaw_iff (W) (ν) : IsUVChannelLaw W ν ↔ ν = ((ν.map fun q ↦ (q.1,q.2.1,q.2.2.1)) ⊗ₘ W.comap …).map (fun z ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2))` | `Region.lean:125` | ✅ **S4 の入口** |
| 入出力の周辺法 | `lemma IsUVChannelLaw.map_input_output {W} [IsMarkovKernel W] {ν} [SFinite ν] (h : IsUVChannelLaw W ν) : ν.map (fun q ↦ (q.2.2.1, q.2.2.2)) = (ν.map fun q ↦ q.2.2.1) ⊗ₘ W` | `Region.lean:228` | ✅ |
| 4 スロット | `uvInfo₁ ν = mutualInfo ν (·.2.1) (·.2.2.2.1)` / `uvInfo₂ ν = mutualInfo ν (·.1) (·.2.2.2.2)` / `uvInfoSum₂ ν [IsFiniteMeasure ν] = uvInfo₂ ν + condMutualInfo ν (·.2.2.1) (·.2.2.2.1) (·.1)` / `uvInfoSum₁ ν [IsFiniteMeasure ν] = uvInfo₁ ν + condMutualInfo ν (·.2.2.1) (·.2.2.2.2) (·.2.1)`。型クラスは `[StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β₁] [Nonempty β₁] [StandardBorelSpace β₂] [Nonempty β₂]` | `OuterBoundUV/Bridge.lean:777` / `:782` / `:787` / `:792` | ✅ |
| 領域 | `def uvRegion (ν) [IsFiniteMeasure ν] : Set (ℝ×ℝ) := {p | InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}` / `def bcOuterRegionUV (W) := closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂)) (_ : IsUVChannelLaw W ↑ν), uvRegion ↑ν)` | `Region.lean:259` / `:271` | ✅ |
| 下方集合 | `theorem bcOuterRegionUV_isLowerSet (W) : IsLowerSet (bcOuterRegionUV W)` / `lemma uvRegion_isLowerSet` | `Region.lean:291` / `:281` | ✅ |
| 4 不等式束 | `structure InBCOuterRegionUV (R₁ R₂ I₁ I₂ J₂ J₁ : ℝ) : Prop` (`bound₁ : R₁ ≤ I₁` / `bound₂ : R₂ ≤ I₂` / `sumBound₂ : R₁+R₂ ≤ J₂` / `sumBound₁ : R₁+R₂ ≤ J₁`) | `OuterBoundUV.lean:735` | ✅ |

### D. 情報量の道具 (DPI / 連鎖律 / 混合) — 既存

| 概念 | 宣言 (逐語) | file:line | S? |
|---|---|---|---|
| 連鎖律 | `theorem mutualInfo_chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) (hXs hYo hZc : Measurable _) : mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc` | `Shannon/CondMutualInfo.lean:214` (`@[entry_point]`) | S4/S5 |
| DPI (無条件) | `theorem mutualInfo_le_of_markov (μ) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (hXs hZc hYo) (hmarkov : IsMarkovChain μ Xs Zc Yo) : mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo` | `Shannon/CondMutualInfo.lean:356` (`@[entry_point]`) | S4 |
| DPI (条件付き) | `theorem condMutualInfo_le_of_markov_joint (μ) [IsProbabilityMeasure μ] (Xs Zc Yo Wc) (hXs hZc hYo hWc) (hmarkov : Shannon.IsMarkovChain μ (fun ω ↦ (Wc ω, Xs ω)) (fun ω ↦ (Wc ω, Zc ω)) Yo) (hWcYo_fin : Shannon.mutualInfo μ Wc Yo ≠ ∞) : Shannon.condMutualInfo μ Xs Yo Wc ≤ Shannon.condMutualInfo μ Zc Yo Wc`。型クラスは 4 型すべてに `[MeasurableSpace _] [StandardBorelSpace _] [Nonempty _]` | `ChannelCoding/ConverseMemorylessChainRule.lean:113` (`@[entry_point]`) | S5 予備 |
| 条件付け変数の挿入 | `lemma condMutualInfo_le_add_condMutualInfo (μ) [IsProbabilityMeasure μ] (A B C Z) (hA hB hC hZ) (hZC : mutualInfo μ Z C ≠ ∞) : condMutualInfo μ A C Z ≤ condMutualInfo μ B C Z + condMutualInfo μ A C (fun ω ↦ (Z ω, B ω))` | `OuterBoundUV/Gateway.lean:194` | S5 予備 |
| 有限性 | `theorem mutualInfo_ne_top [Fintype X] [MeasurableSingletonClass X] [Fintype Y] [MeasurableSingletonClass Y] (μ) [IsProbabilityMeasure μ] (Xs Yo) (hXs hYo) : mutualInfo μ Xs Yo ≠ ∞` / `theorem condMutualInfo_ne_top [Fintype X/Y/Z] [MeasurableSingletonClass X/Y/Z] (μ) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs Yo Zc) (hXs hYo hZc) : condMutualInfo μ Xs Yo Zc ≠ ∞` | `MutualInfo.lean:174` / `CondMutualInfo.lean:320` | 全段 |
| 条件付き MI の分解 | `lemma condMutualInfo_compProd_fst_eq_lintegral [Countable T] [MeasurableSingletonClass T] (μ : Measure T) [IsProbabilityMeasure μ] (κ : Kernel T S) [IsMarkovKernel κ] {f : S → A} {g : S → B} (hf hg) : condMutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) Prod.fst = ∫⁻ t, mutualInfo (κ t) f g ∂μ` | `Shannon/CondMutualInfoMixture.lean:102` | **S5 の裾評価の核** |
| 混合の分解 (無条件) | `lemma mutualInfo_compProd_eq_add_lintegral [Countable T] [MeasurableSingletonClass T] (μ) [IsProbabilityMeasure μ] (κ) [IsMarkovKernel κ] {f g} (hf hg) {tag : A → T} (htag) (hrec : ∀ᵐ p ∂(μ ⊗ₘ κ), tag (f p.2) = p.1) : mutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) = mutualInfo (μ ⊗ₘ κ) Prod.fst (fun p ↦ g p.2) + ∫⁻ t, mutualInfo (κ t) f g ∂μ` | `CondMutualInfoMixture.lean:142` | **S6 の核** |
| 混合の分解 (条件付き) | `lemma condMutualInfo_compProd_snd_eq_lintegral [Countable T] [MeasurableSingletonClass T] {C} [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C] (μ) (κ) {f g h} (hf hg hh) {tag : C → T} (htag) (hrec) (htagfin : mutualInfo (μ ⊗ₘ κ) Prod.fst (fun p ↦ g p.2) ≠ ∞) (hmargfin : (∫⁻ t, mutualInfo (κ t) h g ∂μ) ≠ ∞) : condMutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) (fun p ↦ h p.2) = ∫⁻ t, condMutualInfo (κ t) f g h ∂μ` | `CondMutualInfoMixture.lean:164` | **S6 の核** |
| 再符号化不変 | `mutualInfo_eq_of_leftInverse` / `condMutualInfo_eq_of_leftInverse_cond` | `CondMutualInfoMixture.lean:40` / `:66` | S5 |
| エントロピー上界 | `theorem entropy_le_log_card (μ) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) : entropy μ X ≤ Real.log (Fintype.card α)` | `MaxEntropy/Basic.lean:229` (`@[entry_point]`) | **S5 の裾評価** |
| MI ↔ エントロピー形 | `lemma mutualInfo_toReal_eq_entropy_form {A B} [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B] … (μ) [IsProbabilityMeasure μ] (f : Ω → A) (g : Ω → B) (hf hg) : (mutualInfo μ f g).toReal = entropy μ f + entropy μ g - entropy μ (fun ω ↦ (f ω, g ω))` | `MultipleAccess/Reconciliation.lean:45` | **S3** |
| cMI ↔ 条件付きエントロピー形 | `theorem condMutualInfo_eq_condEntropy_sub_condEntropy (μ) [IsProbabilityMeasure μ] (Xs Yo Zo) (hXs hYo hZo) : (condMutualInfo μ Xs Zo Yo).toReal = MeasureFano.condEntropy μ Xs Yo - MeasureFano.condEntropy μ Xs (fun ω ↦ (Yo ω, Zo ω))` | `Shannon/Entropy.lean:200` (`@[entry_point]`) | **S3** |
| 対のエントロピー分解 | `theorem entropy_pair_eq_entropy_add_condEntropy` | `Shannon/Entropy.lean:42` | S3 |

### E. 時分割の先例 (S8-a、UV 側) — **そのままは効かない**

| 資産 | file:line | S6 との差分 |
|---|---|---|
| `bcUVTimeShare c W = ((bcUVLetterIndexLaw n) ⊗ₘ bcUVLetterKernel c W).map Prod.snd` | `OuterBoundUV/Assembly.lean:258` | **`BroadcastCode` の文字添字専用**。索引が `Fin n` 一様で、混合の重み `λ` を自由に取れない |
| `lemma bcUVTimeShare_uvInfo₁_ge … : (n : ℝ≥0∞)⁻¹ * ∑ i, uvInfo₁ (bcUVJointDistribution c W i) ≤ uvInfo₁ (bcUVTimeShare c W)` (兄弟 3 本 `_uvInfo₂_ge:333` / `_uvInfoSum₂_ge:410` / `_uvInfoSum₁_ge:418`) | `Assembly.lean:315` | 機構 (`mutualInfo_compProd_eq_add_lintegral` + `tag` で索引を補助から復元) は**そのまま流用可**。`tag` の役割は `bcUVLetterKernel_ae_tag` (`:296`) |
| `bcUVTimeShare_isUVChannelLaw` | `Assembly.lean:284` | `IsUVChannelLaw.finsetSum` (`Region.lean:162`) + `.smul` の合成。S6 では不要 |

⟹ **S6 は「S8-a の写経」ではない**。効くのは (a) 汎用の混合法 3 本
(`CondMutualInfoMixture.lean:102/142/164`) と (b) 「索引を補助変数の第 1 成分に持たせて
`tag` で復元する」という**設計パターン**の 2 点。`bcUVTimeShare` そのものは
`BroadcastCode` に張り付いているので S6 では使えない。
**判断ログ 11-(f)「雛形の到達目標が自分と同じ強さか」の適用先**。

---

## Q4 署名案

### 主定理 (第 1 案、推奨)

```lean
/-- Over a less noisy broadcast channel the operational capacity region coincides with the
UV outer region. -/
@[entry_point]
theorem bc_lessNoisy_capacity_eq_uv {α : Type u} {β₁ β₂ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
    [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (hln : IsBCLessNoisy W) :
    bcCapacityRegion W = bcOuterRegionUV W
```

- **主語は `bcCapacityRegion`**。`martonRegionUnionFS` は Q1 で外れたので出てこない。
- `hW` (全支持) は `bc_achievability` の regularity 前提として**逆包含側だけ**に要る。
  順包含 `bc_capacity_subset_uv` は無条件。
- honesty の自己チェック: `IsBCLessNoisy` は `bcCapacityRegion` / `bcOuterRegionUV` を
  **一切参照しない**チャネルレベルの述語 (`Classes.lean:63`)。「等号が成り立つ」に近い形の
  述語ではない。`hW` は全支持の regularity。**load-bearing hyp なし**。
- ⚠ `StandardBorelSpace` は明示不要 — `[Fintype _] [MeasurableSingletonClass _]` から
  instance chain で自動 derive される (Fano Phase 2 の実測と同じ、probe で確認済)。

### 中間 (第 2 案、S2 で先に取れる headline)

```lean
/-- The superposition inner bound of a less noisy broadcast channel is achievable. -/
noncomputable def bcSuperpositionRegionFS (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k : ℕ) (pU : Measure (Marton.bcAuxAlphabet.{u} k))
    (_ : IsProbabilityMeasure pU) (_ : ∀ u, 0 < pU.real {u})
    (K : Kernel (Marton.bcAuxAlphabet.{u} k) α) (_ : IsMarkovKernel K)
    (_ : ∀ u a, 0 < (K u).real {a}),
    {p : ℝ × ℝ | p.1 ≤ bcInfo₁ pU K W ∧ p.2 ≤ bcInfo₂ pU K W})

@[entry_point]
theorem bcSuperpositionRegionFS_subset_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hln : IsBCLessNoisy W) :
    bcSuperpositionRegionFS W ⊆ bcCapacityRegion W
```

### 補助 (第 3 案、S0 の factoring)

```lean
theorem bc_achievability_of_infoJoint_ge
    (pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a})
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})
    (hsum : bcInfo₁ pU K W + bcInfo₂ pU K W ≤ bcInfoJoint pU K W)
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (_hR₂ : 0 < R₂)
    (hR₁lt : R₁ < bcInfo₁ pU K W) (hR₂lt : R₂ < bcInfo₂ pU K W)
    {ε' : ℝ} (hε' : 0 < ε') : …
```

`hsum` の honesty 判定は §Q2-1 の箱を参照。

### 前提が事故りやすい 3 点 (key-preconditions box)

- **`bc_achievability` は `0 < R₁` かつ `0 < R₂` を要求する** (`_hR₂` は未使用だが `hR₁` は
  `bc_Ec_lt_of_rate` の `hR₁ : 0 ≤ R₁` で本質的、`Assembly.lean:1028` の docstring 参照)。
  領域には符号制約がないので**退化点の被覆が別途要る** (§Q3-B の 15 行)。
- **`IsBCLessNoisy` の `U` は `α` と同一 universe の `Fintype`**。`ℕ` にも `ULift.{u} ℕ` にも
  当たらない (§Q2-3 に逐語エラー)。
- **`condMutualInfo_compProd_*_eq_lintegral` は `[Countable T] [MeasurableSingletonClass T]` を
  索引側に要求**し、`tag` による索引復元 `hrec : ∀ᵐ p ∂(μ ⊗ₘ κ), tag (f p.2) = p.1` が要る。
  ⟹ **時分割変数を補助の第 1 成分に埋め込む形でしか使えない**
  (`bcUVLetterKernel_ae_tag`, `Assembly.lean:296` がその実例)。

---

## Mathlib の壁

**0 件**。逆包含に要る道具はすべて in-repo の既存資産か、既存資産の組み合わせで書ける。

参考までに 0-hit を記録 (すべて `loogle --read-index` 実測):

| クエリ | 結果 | 影響 |
|---|---|---|
| `InformationTheory.klDiv, iSup` / `, Monotone` / `, MeasurableSpace.generateFrom` / `, Filter.Tendsto` | 4 本とも `Found 0 declarations` | 「MI = 有限量子化の上限」の一般定理は Mathlib に無い。**ただし要らない** — 裾評価 `≤ P(U≥m)·log\|β₂\|` は初等的に書ける (§Q2-3) |
| `InformationTheory.klDiv _ _ ≤ InformationTheory.klDiv _ _` | `Of these, 0 match your pattern(s)` | KL の DPI は Mathlib に無いが、in-repo の `mutualInfo_le_of_markov` で足りる |
| `Eggleston` (`rg` on Mathlib) | 0 件 | Fenchel–Eggleston は不在。**Carathéodory 路を選ばない**理由 |

存在確認できたもの: `lemma ProbabilityTheory.compProd_map_condDistrib (hY : AEMeasurable Y μ) :
(μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a)`
(`Mathlib/Probability/Kernel/CondDistrib.lean:82`、変数束は
`[MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] {μ : Measure α} [IsFiniteMeasure μ]`) —
S4 で `ν` の `(U,X)` 周辺法を `pU ⊗ₘ K` に開くのに要る。
Carathéodory は `Mathlib/Analysis/Convex/Caratheodory.lean:148` / `:161`。

---

## 撤退ラインとの距離

| slug | 判定 | 根拠 |
|---|---|---|
| **L-BCO7** (semi-deterministic) | **触れない** | 本 leg は less noisy のみ。`hW` を要求する点は同じだが、less noisy には全支持の例 (劣化 BSC 対) が存在する |
| **L-BCO8** (逆包含 `bcOuterRegionUV ⊆ martonRegionUnionFS`) | **発動条件が消滅 (目標が偽)** | Q1 で偽と判定。「濃度上界 (i) / 有限量子化 (ii) のどちらで開くか」という枠組みごと無効。slug は凍結なので文言は残すが、**判定は「不発動ではなく無効化」**。退避先だった `sorry` + `@residual(plan:bc-marton-uv-cardinality-bound)` も**書いてはいけない** — 偽の命題を署名として残すことになる |
| **L-BCO3** (等号が外界の形と噛み合わない) | **発動しない見込み** | 噛み合わせは内界の形の問題。内界を `martonRegionUnionFS` から `bcSuperpositionRegionFS` に差し替えれば解消する (判断ログ 11-(k) の延長) |
| **L-BCO2** (Phase 2 の型量化 union) | **不発動のまま** | `bcAuxAlphabet` は `bcSuperpositionRegionFS` でもそのまま使える (§Q4 第 2 案) |

### 新しい撤退ラインの提案 (親 plan へ、L-BCO9 相当)

- **発動条件**: S5 (有限量子化 + 裾評価) または S6 (時分割の補助への吸収) が閉じない。
- **退避先**: 逆包含 `bc_uv_subset_superposition` を `sorry` +
  `@residual(plan:bc-lessnoisy-converse-quantization)` で**署名を保ったまま**残し、
  S0–S3 の成果だけで leg を閉じる。この時点でも
  `bcSuperpositionRegionFS W ⊆ bcCapacityRegion W ⊆ bcOuterRegionUV W` の挟み込みが
  **less noisy の言葉で** 1 本立つので単独で価値がある。
- **禁止**: `IsLessNoisyTight` / `IsSuperpositionOptimal` のような「等号が成り立つ」を束ねる
  述語は作らない (親 plan §撤退ライン の禁止事項、CLAUDE.md tier 5)。

### 親 plan で書き換えが要る箇所 (本在庫の帰結、編集は plan の担当)

1. §推奨実行順 の「残る包含は `bcOuterRegionUV W ⊆ martonRegionUnionFS W` の 1 本」 → **偽**
2. §Phase 5 の「less noisy … 内界側の全支持仮説とも両立する ⟹ 最も再利用率が高い」 →
   再利用率が高いのは正しいが、**再利用先は Marton ではなく superposition**
3. §Phase 2 の P7 (全支持の除去) の優先度 → Marton 路が外れたので**等号の前提ではなくなる**
   (代わりに superposition 側の全支持摂動 S7 が要る)
4. §撤退ライン L-BCO8 の扱い (上表)
5. §在庫 の「存在しないもの (a) 逆包含 …**等号に残る唯一の包含**」 → 差し替え

---

## 着手のための skeleton

`InformationTheory/Shannon/BroadcastChannel/LessNoisyEquality.lean` の出だし
(import の 2 本並立が cycle を作らないことは probe で機械確認済):

```lean
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Classes
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Assembly

/-!
# Broadcast channel — the capacity region of a less noisy channel

## Main definitions
* `bcSuperpositionRegionFS W` — the superposition inner bound as a union over auxiliary
  alphabets, restricted to the full-support indices.

## Main statements
* `bcSuperpositionRegionFS_subset_capacity` — the superposition inner bound is achievable.
* `bc_lessNoisy_capacity_eq_uv` — the capacity region equals the UV outer region.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal

set_option linter.unusedSectionVars false

universe u

-- variable 束は `MartonUnion.lean:44`–`:47` と逐語同一 (α : Type u + 3 型の Fintype 束)

/-- The superposition inner bound of a broadcast channel, as the closure of the union of the
rectangles `R₁ ≤ I(X; Y₁ ∣ U)`, `R₂ ≤ I(U; Y₂)` over the full-support auxiliary laws. -/
noncomputable def bcSuperpositionRegionFS (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (k : ℕ) (pU : Measure (Marton.bcAuxAlphabet.{u} k))
    (_ : IsProbabilityMeasure pU) (_ : ∀ u, 0 < pU.real {u})
    (K : Kernel (Marton.bcAuxAlphabet.{u} k) α) (_ : IsMarkovKernel K)
    (_ : ∀ u a, 0 < (K u).real {a}),
    {p : ℝ × ℝ | p.1 ≤ bcInfo₁ pU K W ∧ p.2 ≤ bcInfo₂ pU K W})

@[entry_point]
theorem bcSuperpositionRegionFS_subset_capacity (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hln : IsBCLessNoisy W) :
    bcSuperpositionRegionFS W ⊆ bcCapacityRegion W := by
  sorry

theorem bc_uv_subset_superposition (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hln : IsBCLessNoisy W) :
    bcOuterRegionUV W ⊆ bcSuperpositionRegionFS W := by
  sorry

@[entry_point]
theorem bc_lessNoisy_capacity_eq_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hln : IsBCLessNoisy W) :
    bcCapacityRegion W = bcOuterRegionUV W :=
  Set.Subset.antisymm (bc_capacity_subset_uv W)
    ((bc_uv_subset_superposition W hln).trans (bcSuperpositionRegionFS_subset_capacity W hW hln))

end InformationTheory.Shannon.BroadcastChannel
```

⚠ `Marton.bcAuxAlphabet` は `MartonUnion.lean:52` にあり、`MartonUnion.lean` は
`OuterBoundUV/MartonBridge.lean` を import する。上の import 2 本だけでは見えないので、
(a) `MartonUnion.lean` も import する、(b) `bcAuxAlphabet` を `Basic.lean` へ上流移動する、
のどちらか。**(a) が安い** (probe で `Classes` + `MartonUnion` の並立が cycle を作らないことを確認済)。

---

## オーケストレーターのブリーフとの差分

**外れていたもの** (次 leg の判断材料):

1. **【重大】plan の次手 `bcOuterRegionUV ⊆ martonRegionUnionFS` は偽** (§Q1)。
   ブリーフは「偽の公算が高い」と正しく疑っていたが、plan 本体は依然これを唯一の残包含として
   いる。しかも偽なのは外界との比較だけでなく、**`martonRegionUnionFS ⊊ bcCapacityRegion` が
   劣化 BSC 対で成立**する (内界が真に狭い)。
2. **【重大】`IsBCLessNoisy` は `ℕ` 補助に当たらない**。ブリーフの Q2-(2) は
   「`ν` から `b := uvInfo₂ ν` を取り、less noisy から `I(U;Y₁) ≥ I(U;Y₂)`」という順序を
   書いているが、`IsBCLessNoisy` の `∀ (U : Type u) [Fintype U]` に `ℕ` は入らない
   (universe が先に落ちる、逐語エラーは §Q2-3)。**量子化 → less noisy** の順に固定が要る。
3. **`bc_achievability` の署名一般化は「差し替え」より「factor out」が正しい**。
   ブリーフの「`hdeg` を `hln` に差し替えるだけで通る」は probe で PASS したが、
   `IsBCLessNoisy` は `Classes.lean` = `Achievability/Assembly.lean` の**下流**にあるので、
   その場での差し替えは import 方向に反する。共通形へ factor out が要る
   (direct consumer は 3 本とも 0–1 なので波及コストはゼロ、実測は §Q2-1)。
4. **S8-a の平均化はそのままは効かない**。ブリーフは「S8-a が UV 側で同型の平均化を既にやって
   いるのでそのまま効くか」と問うているが、`bcUVTimeShare` (`Assembly.lean:258`) は
   `BroadcastCode` の**文字添字 `Fin n` 一様混合に張り付いて**おり、重み `λ` を自由に取れない。
   流用できるのは汎用の混合法 3 本 (`CondMutualInfoMixture.lean:102/142/164`) と
   「索引を補助の第 1 成分に埋めて `tag` で復元する」設計パターンだけ (§Q3-E)。
5. **`IsUVChannelLaw` から Markov 性を出す既存補題は 0 件**。`rg 'IsMarkovChain' OuterBoundUV/`
   の実測で存在しない (`MartonBridge.lean:307` / `:333` は Marton 結合法専用)。S4 で新規 ~60 行。
   なお行番号はブリーフの `Region.lean:102` / `:123` ではなく **`:104`** (`def IsUVChannelLaw`)
   / **`:125`** (`lemma isUVChannelLaw_iff`)。
6. **`martonInfo*` の `.toReal` 危険は本 leg では発火しない** (判断ログ 17 の再確認)。
   内界を Marton から superposition に差し替えると `I(V₁;V₂)` (補助 × 補助) が消え、
   4 スロットすべてが出力との情報量になるので有限。⟹ 判断ログ 17 の反例 class は
   **superposition 路では構造的に起きない** (これは差分ではなく、ルート変更の副次的な利得)。

**当たっていたもの**: `bc_achievability` が `hdeg` を 1 箇所でしか使っていない /
`V₁=X, V₂=U` の不足量 `h(β*q) - h(β)` / `Y₁` 無雑音のとき差が消える / 裾質量の誤差が
`≤ ε·log|β₂|` 型 / 有限量子化が `I(X;Y₁|U)` を増やし `I(U;Y₂)` を減らす / `λ = R₂/b` の
場合分け + 下方集合性で凸結合が閉じる。

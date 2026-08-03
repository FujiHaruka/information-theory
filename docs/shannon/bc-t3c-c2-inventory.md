# (C2) 側の在庫 — 第 3 次 relay N0 の**差分**と新規調査

> **Parent plan**: [bc-open-problem-t3c-plan.md](bc-open-problem-t3c-plan.md)
> **前 relay の在庫 (⚠ 上書きしない。変わっていない節はここへリンクする)** =
> [bc-t3b-c2-inventory.md](bc-t3b-c2-inventory.md)
> 確定事実の SoT = [`bc-facts.md`](bc-facts.md) の `## L0 (T3)` / `## L2 (T3)` / `## M6 (T3b)` /
> `## M19 (T3b)` 節。⚠ **本ファイルはそこから値を複製しない — 参照する**。
>
> **leg 冒頭宣言 (N0)**: 側 = (C2) / 動かすもの = 前 relay の資産 (検証器・一次文献) の生存を機械で
> 確認し、N1 / N2 が消費する在庫だけを**結論形で**取り直して、両 leg が在庫の空振りで溶けないようにする

---

## 0. 一行サマリ

**N1 の在庫は満杯、N2 の在庫は 3 つのうち 2 つが「思っていたより在る」。**
資産は **16 本の一次文献・5 系統の検証器がすべて生存し、実行して再現した** (§1)。
N2 の 3 標的のうち **(α) は Mathlib に既存の受け皿 `iCondIndepFun` があり、13 変数の周囲空間で
実際に型検査が通った** (§3.1、実測) / **(γ) は in-project に 11 本の 2 レート領域 def が在るが
`Thm7` に当たるものは依然 0 本で、しかも既存 UV 領域の `closure` は「実効コンパクト性の証拠を
1 つも運ばない」ことが判明した** (§3.3) / **(β) だけが本物の空白**で、`Computable` と
`TopologicalSpace` を同時に言及する Mathlib 宣言は **0 件**である (§3.2)。

⭐ **§2.5 の設計軸は一次文献 diff で形が変わった** (§4) — **ゴールの主語 ([N13] / [Li21]) は
2 レートである** (逐語)。3 レートなのは `Thm7` / `Thm8` / GK-Bound / UVW 外界の側で、
**[egk4] は「UVW 外界の `R₀=0` スライスは 2 レートの簡単な領域と *等しい*」と述べており、
その簡単な領域の形は in-project の `uvRegion` の形そのもの**である。⚠ **これは UV 族についての
記述であって `Thm7` には移らない**。⚠ **スライスの effective compactness が従うとは書かない** (§4.3)。

---

## 1. (I) 資産の生存確認 — 全件生存、実行して再現

`SP=/private/tmp/claude-502/-Users-haruka-dev-lean-projects/d6d1ee1c-b8f7-4b1b-9f17-e7eb0b9e0627/scratchpad`
(⚠ **本セッションの scratchpad と同一パス**。plan §4.9 の定型どおり)

| 資産 | 生存 | 実測 (⚠ 出力の抜粋) |
|---|---|---|
| `m6/m6_verify.py` (`R ∈ C` 3 経路一括) | ✅ **実行して再現** | `route 1 [probc] Thm 3 (= C, closed form) : min slack +0.00000000 -> R in C : True` / `route 2 Thm8 (31a)-(31g) at (Y1,Z2) : min slack +0.00000000 -> R in Thm8 : True` / `route 3 [probc] (8) Marton inner (no mirror) : min slack +0.00000000 -> R achievable: True` / `VERDICT: R IS IN the Thm8 region of (G,K) = (Y1,Z2) [all three routes agree]` / `ceiling of R0+R1 on the sum-rate face of C = 0.89160926 ; R1 = 0.75575882` |
| `m6/lib6.py` (`C` の閉形評価器) | ✅ import OK (31 public names) | `m6_verify.py` が呼ぶ |
| `m14/step0.py` (較正 4 本) | ✅ **4 本とも再現** | (a) `(18a..18i) = [0,1,2,1,1,2,1,2,2]` (期待値一致) / `(31a..31g) = [0,1,1,1,1,2,2]` (一致) / `eligibility max violation = 0.000e+00` / `Sa..Sg` 7 本とも `0.0` ・ (b) `C=0.5310044` / `2C=1.0620088` / `d* = 0.03877137 at alpha = 0.077670` / `SR_C = 1.1007802` / 乱択 20000 本 `max I(X;Y) = 1.0616639` ・ (c) `(Y1,Z2)` の 5 kind 表を再現 ・ (d) 鏡映残差 `0.000e+00` |
| `m14/lib14.py` | ✅ import OK (44 public names) | ⚠ **`JKINDS = ('const','X','G','K','GK')` = 5 種のみ** (§2 参照) |
| `m13/m10_fast.py` (Thm7/Thm8 高速評価器) | ✅ import OK (23 public names) | `obligations` / `elig7` / `thm7` / `thm8` / `R1SET` / `R2SET` を持つ |
| `m15/m15_fast.py` + `m15_repro.py` | ✅ **反例を再実行して再現** | `reproduced trial 0 in 141s` / `Sc = +0.03835493  A = +0.03835493  eq = 1.33e-15  min (20) slack = +0.030669  rate slack = +0.502951` / `saved viol_hat.npy ((4,4,4,4)) / viol_tilde.npy ((4,4,4,4))` |
| `m15/viol_hat.npy` / `viol_tilde.npy` / `viol.npy` | ✅ | `shape=(4,4,4,4) dtype=float64 finite=True` ×2 / `shape=(64,)` |
| `m15audit/aud.py` + `g67.py` (独立評価器) | ✅ **11 種 `T_J` 表を実行して再現** | `Y1: |19|max 2.136e-13, min(20) +0.030669, (20c) +9.992e-16 → YES` / `Z2: 2.132e-13, +0.148429, +8.882e-16 → YES` / **他 9 種はすべて `no`** (`const/X/X1/X2/Y2/Z1/Y/Z/GK`)。⭐ `(18h)` だけ `J` スプレッド `1.18e-01`、他 8 本は `≤ 1.33e-15` |
| `lit/` 一次文献 | ✅ **16 本** | `auxrec(2951) BC-it07(563) bsp(1495) cpt(1083) dou24(779) egk(26) egk4(30390) ggny11(1545) GK-outer(865) jn09(785) li21(1401) loc-ten-bin(395) n13(797) probc(1540) sct(2536) sumofbc(595)` 行 |
| **一次文献の行番号 抜き取り検査 2 箇所** | ✅ **2 箇所とも facts の引用と一致** | `auxrec.txt:1069-1071` = `R0 + R1 + R2 ≤ min I(W ; Y ), I(W ; Z)` / `+ min I(V ; Z\|W ) + I(X; Y \|V, W ), I(U ; Y \|W ) + I(X; Z\|U, W ) , (18i)` ・ `probc.txt:558-560` = `Theorem 3. The capacity region for a product of reversely more-capable (say, receiver Z1 is more / capable than Y1 , and receiver Y2 is more capable than Z2 ) broadcast channel is given by the union of / rate triples satisfying` |

⟹ **再生成は 1 件も行っていない** (plan §4.9 の「検証器を作り直すと 1 leg 溶ける」を発火させていない)。

---

## 2. (II-a) N1 が消費する在庫 — 足りないものは 1 つだけ

N1 の問い = 「`(18b),(18c),(18d)` を同時に `0.89160926` より上げたまま、**11 種の `T_J` すべてで**
適格性を保ち `(18i) = SR_C` を維持できるか」(facts `## M19 (T3b)` M19-4 が SoT)。

| N1 が要るもの | 現物 | 足りるか |
|---|---|---|
| Thm7 `(18a)`–`(18i)` の評価 | `m13/m10_fast.thm7` / `m14/lib14` / **`m15audit/aud.py:159 thm7`** | ✅ 3 実装 |
| 適格性 `(19)` / `(20)` / `(20c)` | `m14/lib14.elig_all` / `m15audit/aud.py:188 e19, :202 e20, :213 e20c` | ✅ 2 実装 |
| `R₀+R₁` を押さえる制約集合 | `aud.py:245 R1SET = ('18b','18c','18d','18h','18i')` (M15 独立監査で逐語一致を確認済) | ✅ |
| `C` 側の天井 `0.89160926` | `m6/lib6` + `m6/m6_step1.py` (B) 節 | ✅ 閉形 |
| **11 種の `T_J` 列挙** | ⚠ **`m15audit/g67.py:50` の 1 箇所だけ** — `('const','X','X1','X2','Y1','Y2','Z1','Z2','Y','Z','GK')`。**`m14/lib14.JKINDS` は 5 種** (`const/X/G/K/GK`)、`aud.py:57 Jker(kind)` が 11 種のカーネルを持つ | ⚠ **足りるが、実装が 1 本しかない**。⟹ **N1 は `lib14` 側で回すと 5 種しか見ない** |

**⚠ 前 plan §4.9 の但し書きの読み違いを 1 件塞いだ**: 「`aud.py` は `(31a)`–`(31e)` しか持たない」は
**Theorem 8 の側についての限定**である (`aud.py:219-240`)。**Theorem 7 の側は `(18a)`–`(18i)` の
9 本すべて + `(19)` + `(20)` + `(20c)` を持っている** (`aud.py:157-217`) ので、
**N1 の主戦場 (Thm7 側) では `aud.py` が最も完全な評価器である**。

**Mathlib 在庫は N1 に関係しない** (深追いしていない)。

---

## 3. (II-b) N2 が消費する在庫 — (α)(β)(γ) を結論形で

### 3.1 (α) 9 補助変数の法則述語 — ⭐ **判定 = 在る (Mathlib に受け皿がある)**

**一次文献の逐語 (`auxrec.txt:1073-1074`)**:

```
for some choice of distribution over the variables
   pU,V,W,Ũ,Ṽ,W̃,Û,V̂,Ŵ,X,Y,Z,J = pU,V,W,X · pW̃,Ũ,Ṽ|X · pŴ,Û,V̂|X · TY,Z|X · TJ|X,Y,Z
```

⟹ **補助 9 本 + `X,Y,Z,J` = 13 変数**。構造は「**3 つの補助 3 つ組が `X` 条件付きで互いに独立**」
+「`(Y,Z)` は `X` にのみ依存」+「`J` は `(X,Y,Z)` にのみ依存」の 3 節である。
⚠ **1 本の合成積 (`⊗ₘ`) の等式ではない** — in-project `IsUVChannelLaw` の形とは別物である。

| 概念 | API | file:line | 逐語署名 (`#check` の実出力、`[...]` を落とさない) | 結論形 | (C2) での扱い |
|---|---|---|---|---|---|
| **多変数の条件付き独立** | **`ProbabilityTheory.iCondIndepFun`** | `Mathlib/Probability/Independence/Conditional.lean:145` | `@iCondIndepFun : {Ω : Type u_1} → {ι : Type u_2} → (m' : MeasurableSpace Ω) → {mΩ : MeasurableSpace Ω} → [StandardBorelSpace Ω] → m' ≤ mΩ → {β : ι → Type u_3} → [m : (x : ι) → MeasurableSpace (β x)] → ((x : ι) → Ω → β x) → (μ : autoParam (Measure Ω) iCondIndepFun._auto_1) → [IsFiniteMeasure μ] → Prop` | `Prop` (本体 `Kernel.iIndepFun f (condExpKernel μ m') (μ.trim hm')`) | ⭐ **(α) の受け皿の中核**。⚠ **条件づけの対象は確率変数ではなく部分 σ-加法族 `m'`** ⟹ `X` で条件づけるには `MeasurableSpace.comap xProj inferInstance` を渡す |
| 多変数 ⟹ 2 変数 | `ProbabilityTheory.iCondIndepFun.condIndepFun` | 同 (family、28 decl) | `∀ {Ω ι} {m' mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ] {β : ι → Type u_3} {m : (x : ι) → MeasurableSpace (β x)} {f : (i : ι) → Ω → β i}, iCondIndepFun m' hm' f μ → ∀ {i j : ι}, i ≠ j → CondIndepFun m' hm' (f i) (f j) μ` | `CondIndepFun m' hm' (f i) (f j) μ` | 対ごとの取り出しが 1 行 (実測、§3.4 の T-α2) |
| 言い換え | `ProbabilityTheory.iCondIndepFun_iff_iCondIndep` | 同 | `… iCondIndepFun m' hm' f μ ↔ iCondIndep m' hm' (fun x => MeasurableSpace.comap (f x) (m x)) μ` | `↔` | σ-加法族版へ移る |
| **in-project の 3 項マルコフ連鎖** | `InformationTheory.Shannon.IsMarkovChain` | `InformationTheory/Shannon/CondMutualInfo.lean:92` | `@IsMarkovChain : {Ω} → [MeasurableSpace Ω] → {X} → [MeasurableSpace X] → {Y} → [MeasurableSpace Y] → {Z} → [MeasurableSpace Z] → (μ : Measure Ω) → [IsFiniteMeasure μ] → [StandardBorelSpace X] → [Nonempty X] → [StandardBorelSpace Y] → [Nonempty Y] → (Ω → X) → (Ω → Z) → (Ω → Y) → Prop` | 本体 `μ.map (fun ω ↦ (Zc ω, Xs ω, Yo ω)) = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ))` | ⭐ **写像を引数に取る**ので入れ子タプルの射影を書かずに済む。⚠ **2 分岐 (対ごと) であって 3 分岐の相互独立ではない** |
| in-project の 5 つ組法則 | `…BroadcastChannel.IsUVChannelLaw` | `InformationTheory/Shannon/BroadcastChannel/OuterBoundUV/Region.lean:116` | `@BroadcastChannel.IsUVChannelLaw : {α} → [MeasurableSpace α] → {β₁} → [MeasurableSpace β₁] → {β₂} → [MeasurableSpace β₂] → {U V} → [MeasurableSpace U] → [MeasurableSpace V] → BCChannel α β₁ β₂ → Measure (U × V × α × β₁ × β₂) → Prop` | 本体 `ν.map (fun q ↦ ((q.1,q.2.1,q.2.2.1), q.2.2.2)) = (ν.map fun q ↦ (q.1,q.2.1,q.2.2.1)) ⊗ₘ W.comap …` | ⚠ **拡張の対象にしない** — §5-2 参照 (**直接消費者 64 decl / 8 file**、実測) |
| 5 つ組法則の補助 (射影の可測性) | `measurable_uvFirstThree` / `measurable_uvSplit` / `measurable_uvUnsplit` | 同 `:121` / `:126` / `:130` | `private`、いずれも `measurable_fst`/`measurable_snd` の手組み入れ子 | `Measurable (fun q : U × V × α × β₁ × β₂ ↦ …)` | ⚠ **13 変数へ持ち上げると組合せ的に増える** ⟹ (α) をこの形で書かない理由 |

**⭐ 実測 (反証を試みた型検査。§4.1 軸 1 の処方)**: `scratchpad/n0/n0_alpha.lean` — 13 タプルの周囲空間
`Om := (A×A×A) × (A×A×A) × (A×A×A) × Xa × Ya × Za × Ja` の上で

- **(T-α1)** `iCondIndepFun mX mX_le auxTriple μ` (`mX := MeasurableSpace.comap xProj inferInstance`) が **通る**
- **(T-α2)** `h.condIndepFun (by decide)` で 3 分岐 ⟹ 対ごとの取り出しが **1 行で通る**

⟹ `lake env lean` の**出力 0 バイト**。

⚠ **残る債務 2 件 (本 leg は決着させない)**:
1. **合致の証明** — 「`iCondIndepFun` の 1 節 + `(Y,Z)` 節 + `J` 節の**連言**が `auxrec.txt:1074` の
   因子分解と同値である」は**まだ示していない**。⚠ **「従う」と書かない**。
2. **`[StandardBorelSpace Ω]` が 13 タプル全体に要る** — in-project の BC 家系は
   `[StandardBorelSpace α] [Nonempty α]` を**因子ごと**に持つ形なので、積への持ち上げが要る (§6)。

### 3.2 (β) 量化子補題 (L-∃) / (L-∀) — ⚠ **判定 = 無い (ただし古典版は全部在る)**

⚠ **前 relay の §6 W2 を追認していない** — **二段階の結論形検索**と**テンプレート補題の名指し**を通した。

**第 1 段 (生クエリ、⚠ これだけを根拠にしない)**:

| クエリ | 結果 |
|---|---|
| `REPred, IsCompact` | `Found 0 declarations mentioning REPred and IsCompact.` |
| `REPred, IsClosed` | `Found 0 declarations mentioning IsClosed and REPred.` |
| `REPred, Set` | `Found 0 declarations mentioning REPred and Set.` |
| `Partrec, IsCompact` | `Found 0 declarations mentioning IsCompact and Partrec.` |

**第 2 段 (結論形 / 層の交差、⭐ これが決め手)**:

| クエリ (層の交差) | 結果 | 読み |
|---|---|---|
| `Computable, TopologicalSpace` | **`Found 0`** | ⭐ **Mathlib の計算可能性層と位相層は 1 宣言も交わらない** |
| `Primcodable, TopologicalSpace` | **`Found 0`** | 同上 |
| `Computable, Metric.ball` | **`Found 0`** | 有理球による近似の層が無い |
| `Partrec, Metric.ball` | **`Found 0`** | 同上 |
| `TopologicalSpace.IsTopologicalBasis, Computable` | **`Found 0`** | 計算可能な基底の概念が無い |
| `REPred` (全宣言) | **`Found 8 declarations`** (`REPred` / `ComputablePred.to_re` / `REPred.of_eq` / `ComputablePred.computable_iff_re_compl_re'` / `Partrec.dom_re` / `ComputablePred.computable_iff_re_compl_re` / `ComputablePred.halting_problem_re` / `ComputablePred.halting_problem_not_re`) | ⭐ **c.e. 述語の API はこの 8 本で全部**である |
| `\|- REPred _` | `Found 8 … Of these, 4 match` | 生成則は 4 本のみ |

**in-project (⚠ loogle は Mathlib しか見ない。`rg` で自プロジェクトを引いた)**:

- `rg -ni 'semicomput\|effectively compact\|computably'` → **`Kolmogorov/OmegaNoncomputable.lean` の 4 行のみ**、
  いずれも**散文** (`:5`, `:35`, `:537`, `:572`)。宣言は 0。
- `Computable|Primrec|Partrec|REPred|Primcodable` を宣言行に含む decl = **31 件 / 9 file**、
  **全件 `Shannon/Kolmogorov/` 配下**。`ℝ` / `Set` / 測度に触れるものは 0 件。
- `rg 'IsCompact' InformationTheory/Shannon/BroadcastChannel/` → **0 件**。
- `scripts/dep_consumers.sh` は (β) に対応する in-project decl が存在しないので引けない。

**⭐ テンプレート補題の名指し (壁判定の必要条件 (b))** — **古典版は Mathlib に完備している**:

| 段 | Mathlib API | file:line | 逐語署名 | 結論形 |
|---|---|---|---|---|
| **(L-∃) の古典版** | `isClosedMap_fst_of_compactSpace` | `Mathlib/Topology/Maps/Proper/Basic.lean:332` | `∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace Y], IsClosedMap Prod.fst` | `IsClosedMap Prod.fst` |
| 同・proper 版 | `isProperMap_fst_of_compactSpace` | 同 `:322` | `[CompactSpace Y] : IsProperMap (Prod.fst : X × Y → X)` | `IsProperMap Prod.fst` |
| **(L-∀) の古典版** | `isClosed_iInter` | `Mathlib/Topology/Basic.lean:147` | `∀ {X : Type u_1} {ι : Sort u_2} [inst : TopologicalSpace X] {f : ι → Set X}, (∀ (i : ι), IsClosed (f i)) → IsClosed (⋂ i, f i)` | `IsClosed (⋂ i, f i)` |
| witness 空間のコンパクト性 (単体) | `isCompact_stdSimplex` | `Mathlib/Analysis/Convex/StdSimplex.lean:189` | `∀ (𝕜 : Type u_1) (ι : Type u_2) [inst : Fintype ι] [inst_1 : TopologicalSpace 𝕜] [inst_2 : Semiring 𝕜] [inst_3 : PartialOrder 𝕜] [OrderClosedTopology 𝕜] [ContinuousAdd 𝕜] [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜], IsCompact (stdSimplex 𝕜 ι)` | `IsCompact (stdSimplex 𝕜 ι)` |
| 同・`CompactSpace` インスタンス | `stdSimplex.instCompactSpace_coe` | 同 `:193` | `∀ (𝕜 : Type u_1) (ι : Type u_2) [Fintype ι] [TopologicalSpace 𝕜] [Semiring 𝕜] [PartialOrder 𝕜] [OrderClosedTopology 𝕜] [ContinuousAdd 𝕜] [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜], CompactSpace ↑(stdSimplex 𝕜 ι)` | `CompactSpace ↑(stdSimplex 𝕜 ι)` |
| **確率測度の空間のコンパクト性** | `instCompactSpaceProbabilityMeasure` | `Mathlib/MeasureTheory/Measure/Prokhorov.lean:167` | `instance [CompactSpace E] : CompactSpace (ProbabilityMeasure E)` (節の変数 = `{E : Type*} [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]`、`:65`) | `CompactSpace (ProbabilityMeasure E)` |
| in-project の単体コンパクト性の実例 | `isCompact_cornerSimplex` | `InformationTheory/Shannon/Portfolio/Universal.lean:126` | `theorem isCompact_cornerSimplex : IsCompact (cornerSimplex d)` | `IsCompact (cornerSimplex d)`。**本体 14 行** (`:126-139`、`Metric.isCompact_of_isClosed_isBounded` 経由) |

**⭐ 実測 (`scratchpad/n0/n0_probe.lean`、`lake env lean` で 5/6 が通り 1 本が期待どおり落ちた)**:

| # | 試した主張 | 結果 |
|---|---|---|
| P1 | `CompactSpace (stdSimplex ℝ (Fin 5))` | ✅ **通った** (`inferInstance`) |
| P2 | `CompactSpace (stdSimplex ℝ (Fin 5) × stdSimplex ℝ (Fin 3))` | ✅ **通った** |
| P3 | 古典 (L-∃): `[CompactSpace Y] (hR : IsClosed R) : IsClosed (Prod.fst '' R)` | ✅ **通った** (`isClosedMap_fst_of_compactSpace _ hR`、**1 行**) |
| P4 | 古典 (L-∀): `(hR : IsClosed R) : IsClosed {x \| ∀ y : Y, (x,y) ∈ R}` | ✅ **通った** (`isClosed_iInter` 経由、**4 行**)。⚠ **`Y` にコンパクト性も overtness も要らない** |
| P5 | `CompactSpace (ProbabilityMeasure (Fin 3 × Fin 4))` | ✅ **通った** |
| P6 | `CompactSpace (ProbabilityMeasure (ℕ × ℕ × Fin 2 × Fin 2 × Fin 2))` | ❌ **拒否**: `failed to synthesize instance of type class CompactSpace (ProbabilityMeasure (ℕ × ℕ × Fin 2 × Fin 2 × Fin 2))` ⟹ ⚠ **in-project `bcOuterRegionUV` が量化している添字型はコンパクトでない** (§3.3) |

**⟹ 判定**: **(β) の「実効的 (c.e. / Π01) な」版は Mathlib にも in-project にも無い**。
⚠ **しかし「テンプレートが無い」ではない** — 古典版の連鎖は**そのまま通る**ので、詰まっているのは
**「実効性の層」1 枚だけ**である。⚠ **これは配線 (plumbing) ではなく本物の欠落**である
(層が 1 宣言も交わらない = §3.2 第 2 段)。

**自前実装の分解 (⚠ 行数の前に何を分解したかを書く。prose 見積りを禁ずる §4.1 軸 2)**。
一次文献の証明 ([AH] Proposition 2.5、`sct.txt:261-298` 逐語) は 4 段で、Lean 側の義務はこう割れる:

| 段 | 一次文献の逐語 | Lean 側で新しく要るもの | 既存で足りるもの |
|---|---|---|---|
| (β-1) | "computable T0-space … rational balls" | **`RatBall3 := (ℚ × ℚ × ℚ) × ℚ` と `ratBall3Set` の 2 def** (3 レート版。2 レート版は前在庫 §8 で型検査済) | `Primcodable ℚ` (導出可)、`Metric.ball` |
| (β-2) | "R = ⋃_{(i,j)∈E} B_i^X × B_j^Y, E c.e." | **積基底の添字の対応 1 def + その `Primcodable` 1 instance** | `Primcodable` の積 instance |
| (β-3) | "As Y is effectively compact, F is a c.e. set" (`F` = `Y` を覆う `E` の有限部分集合の族) | ⭐ **witness 空間の effective compactness 1 定理** — 単体の直積が「有限有理被覆が c.e.」を満たすこと。⚠ **これが本体**。近い実例 = `isCompact_cornerSimplex` (**14 行**) だが、それは**古典的コンパクト性**であって c.e. 性を 1 行も含まない | `isCompact_stdSimplex` / `stdSimplex.instCompactSpace_coe` (古典側だけ) |
| (β-4) | "R∀ = ⋃_{L∈F} U_L, which is an effective open set" | **`REPred` の合成則 3〜4 補題** (c.e. 添字上の可算和 / 有限リストの探索) | `REPred` の 8 本のうち生成則は 4 本 (`ComputablePred.to_re` / `REPred.of_eq` / `Partrec.dom_re` / `halting_problem_re`) ⟹ ⚠ **和と有限探索の閉包則は無い** |

⚠ **(L-∀) は [AH] Proposition 2.5 の項目 2 とは別物である** — 項目 2 は「`R` が**実効開**、`Y` が
**実効コンパクト**」の版であり、facts `## L2 (T3)` 行 6 が使う (L-∀) は「`R` が **Π01**、`Y` が
**computably overt**」の版で、**facts 自身が「我々の証明」と明記している**。
⟹ **(β) は 2 本ではなく (L-∃) 1 本 + (L-∀) 1 本 + overtness の述語 1 本**である。

### 3.3 (γ) 領域としての `Thm7(W)` / UV 外界の def — ⚠ **判定 = `Thm7` 側は 0 本、UV 側は在るが形が違う**

**in-project の領域 def を結論形 (`Set (ℝ × ℝ)`) で数え直した (⚠ 前在庫 §2.2 は 8 本と書いたが 11 本ある)**:

`rg -U '(noncomputable )?def …: Set \(ℝ × ℝ\) :=' InformationTheory/Shannon/BroadcastChannel/` →
`bcCapacityRegion` / `bcOuterRegionCoop` / `bcOuterRegionUV` / **`bcSuperpositionRegionNoSumRate`** /
**`bcSuperpositionRegionSumRate`** / `martonRegion` / `martonRegionUnion` /
**`martonRegionUnionFullSupport`** / `martonRegionUnionBounded` / `martonRegionUnionOuterBounded` /
`uvRegion` = **11 本** (太字 3 本が前在庫に無い)。
`rg 'Set \(ℝ × ℝ × ℝ\)' InformationTheory/` → **0 件** (3 レート領域は依然 0 本)。

| 対象 | file:line | 逐語署名 (`#check` の実出力) | 本体 (逐語) | (C2) での扱い |
|---|---|---|---|---|
| UV 外界 (領域) | `OuterBoundUV/Region.lean:425` | `@BroadcastChannel.bcOuterRegionUV : {α} → [MeasurableSpace α] → {β₁} → [MeasurableSpace β₁] → {β₂} → [MeasurableSpace β₂] → [StandardBorelSpace α] → [Nonempty α] → [StandardBorelSpace β₁] → [Nonempty β₁] → [StandardBorelSpace β₂] → [Nonempty β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)` | `closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂)) (_ : IsUVChannelLaw W ν), uvRegion ν)` | ⚠ **補助アルファベットが `ℕ` 固定**で、**基数境界を持たない** ⟹ P6 が示すとおり添字型がコンパクトでない |
| UV の 1 法則分 | 同 `:413` | `@BroadcastChannel.uvRegion : … → [StandardBorelSpace α] → [Nonempty α] → [StandardBorelSpace β₁] → [Nonempty β₁] → [StandardBorelSpace β₂] → [Nonempty β₂] → {U V} → [MeasurableSpace U] → [MeasurableSpace V] → (ν : Measure (U × V × α × β₁ × β₂)) → [IsFiniteMeasure ν] → Set (ℝ × ℝ)` | `{p \| InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}` | 制約束は `InBCOuterRegionUV` (`OuterBoundUV.lean:735`) |
| **⚠ 閉性** | 同 `:431` | `@…bcOuterRegionUV_isClosed : … (W : BCChannel α β₁ β₂), IsClosed (bcOuterRegionUV W)` | **`:= isClosed_closure`** | ⚠⚠ **証明本体が `isClosed_closure` の 1 語** ⟹ **def が `closure` だから閉じているだけ**で、**制約から出た閉性ではない** ⟹ **実効コンパクト性の証拠を 1 つも運ばない**。⚠ docstring 逐語も「a union of closed half-plane intersections **need not be closed**」と、閉包を取る理由を明記している |
| 下方集合性 | 同 `:445` | `@…bcOuterRegionUV_isLowerSet : … IsLowerSet (bcOuterRegionUV W)` | `IsLowerSet.closure (isLowerSet_iUnion …)` | 実効コンパクト性には効かない (有界性が別途要る) |
| 非空性 | 同 `:469` | `@…bcOuterRegionUV_nonempty : … [IsMarkovKernel W] → (bcOuterRegionUV W).Nonempty` | 明示 witness `uvConstLaw W x₀` | 退化境界の確認用 |
| **基数を切った領域の先例** | `Marton/RegionCardinality.lean:270` | `@BroadcastChannel.Marton.martonRegionUnionBounded : {α β₁ β₂} → [Fintype α] → [MeasurableSpace α] → [Fintype β₁] → [MeasurableSpace β₁] → [Fintype β₂] → [MeasurableSpace β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)` | `closure (⋃ (k₁) (_ : k₁ < martonAuxBound α) (k₂) (_ : k₂ < martonAuxBound α) (pV : Measure (bcAuxAlphabet k₁ × bcAuxAlphabet k₂)) (_ : IsProbabilityMeasure pV) (K : Kernel …) (_ : IsMarkovKernel K), martonRegion pV K W)` | ⭐ **「基数境界で切った ⋃」の唯一の in-project 先例**。⚠ **それでも `closure` を取っている**ので、コンパクト性の証明を 1 行も含まない |
| 補助アルファベット | `MartonUnion.lean:67` | `abbrev bcAuxAlphabet (k : ℕ) : Type u := ULift.{u} (Fin (k + 1))` | — | 有限 ⟹ `CompactSpace` が付く側 |
| 基数の上限 | `Marton/CardinalityBound.lean:435` | `def martonAuxBound (α : Type*) [Fintype α] : ℕ := Fintype.card α` | — | ⚠ Thm7 の上限は `\|X\|+6` / `\|X\|+1` (`auxrec.txt:1083-1084`) で**別の値** |
| **`Thm7` に当たる領域 def** | — | — | — | ❌ **依然 0 本** (`rg` + `#check` で再確認) |
| **3 レートの領域 def** | — | — | — | ❌ **0 本** (`Set (ℝ × ℝ × ℝ)` は project 全体で 0 ヒット) |

**⭐ 本 leg の最重要所見 (γ)**: **「領域 def が在る」ことと「実効コンパクト性の証拠が在る」ことは
in-project では完全に分離している**。11 本の領域はすべて `closure (⋃ …)` で閉性を**定義で**得ており、
facts `## L2 (T3)` 行 6 の 6 段が要求する「制約が Π01 ⟹ 量化子を潰しても Π01」という道は
**1 本も通っていない**。⚠ **前在庫 §7 の「詰まっているのは `Thm7` 側の対象の不在であって受け皿の
不在ではない」は、UV 側についても半分しか正しくない** — UV 側の**領域 def は在るが、
実効コンパクト性の受け皿としては使えない形**である。

### 3.4 実測の一覧 (本 leg で `lake env lean` に掛けたもの)

⚠ **`InformationTheory/` へは 1 行も書いていない** (在庫エージェントの編集境界)。
ファイルは `scratchpad/n0/` にある。

| # | 試した主張 | 結果 |
|---|---|---|
| P1–P6 | §3.2 の表のとおり | 5 通り / 1 本が**期待どおり**落ちた (P6) |
| T-α1 | 13 タプル上で `iCondIndepFun mX mX_le auxTriple μ` が書ける | ✅ **通った** (`n0_alpha.lean`、**出力 0 バイト**) |
| T-α2 | 3 分岐の相互独立から対ごとの `CondIndepFun` が 1 行で出る | ✅ **通った** (`h.condIndepFun (by decide)`) |
| S1 | §3.1 / §3.2 / §3.3 の全署名を `#check` で逐語取得 | ✅ (`n0_sig.lean`) |

---

## 4. (III) ⭐ §2.5 の一次文献 diff — 「3 レートか 2 レートか」を逐語で

⚠ **本 leg は軸を決着させない**。diff を取って N2 へ渡すのが仕事である (plan §5 の N0 行)。

### 4.1 レートの次元 — 逐語

| 対象 | 次元 | 逐語 (file:line) |
|---|---|---|
| **[N13] = §0 のゴールの主語** | ⭐ **2 レート** | `n13.txt:43-44` 「Let the channel have an input alphabet X and output alphabets Y, Z respectively. … **A rate pair (R1 , R2 ) is said to be achievable** if there exists a sequence of codes consisting of」/ `n13.txt:65-67` 「The closure of the set of all achievable **rate pairs** is known as the capacity region. **A computable characterization of the capacity region for the two-receiver broadcast channel is still unknown**」 |
| **[Li21] §VIII open problem** (facts `## L3 (T3)` が (C2) と同一の穴と確定させたもの) | ⭐ **2 レート** | `li21.txt:1141-1142` 「the capacity region of the broadcast channel pY,Z\|X can be expressed as a first-order formula (**with free variables X, Y, Z, W1 , W2 , where Wi represents the rate Ri via Ri = H(Wi )**) in that level?」/ `li21.txt:857` 「**rate pair (R1 , R2 )** is achievable for the broadcast channel」 |
| **[auxrec] Theorem 7** | **3 レート** | `auxrec.txt:1034-1035` 「Given a broadcast channel characterized by T (y, z\|x) and any achievable **rate triple (R0 , R1 , R2 )**, one can find some input distribution p(x) such that **for any auxiliary channel TJ\|X,Y,Z**」 |
| **[auxrec] Theorem 8** | **3 レート** | `auxrec.txt:1395-1396` 「Given a broadcast channel T (y, z\|x) and **any** TĴ,J\|X,Y,Z any achievable non-negative **rate triple (R0 , R1 , R2 )** must satisfy」 |
| **[GK-outer] Theorem 7 (GK-Bound)** | **3 レート** | `GK-outer.txt:444-445` 「Given a broadcast channel characterized by TY,Z\|X and any achievable **rate triple (R0 , R1 , R2 )**, one can find some input distribution p(x) such that for any auxiliary channel TG,K\|X,Y,Z」 |
| **UVW 外界 (原形)** | **3 レート** | `BC-it07.txt:36-45` Theorem 2.1「The set of **rate triples (R0 , R1 , R2 )** satisfying `R0 ≤ min{I(W ; Y ), I(W ; Z)}` / `R0 + R1 ≤ I(U, W ; Y )` / `R0 + R2 ≤ I(V, W ; Z)` / `R0+R1+R2 ≤ I(U,W;Y)+I(V;Z\|U,W)` / `R0+R1+R2 ≤ I(V,W;Z)+I(U;Y\|V,W)`」/ `GK-outer.txt:56-57` が基数境界つきで再掲「it suffices to consider (U, V, W ) satisfying **\|W\| ≤ \|X\| + 5, \|U\| ≤ \|X\| + 1, \|V\| ≤ \|X\| + 1**」 |
| **UVW 外界の `R₀ = 0` スライス** | **2 レート** | `BC-it07.txt:201-204` 「Note that the outer bound given in Theorem 2.1 **immediately leads to** the following outer bound for the case when there is no common information, i.e., **R0 = 0**.」⟹ (3.1) は `R1 ≤ I(U,W;Y)` / `R2 ≤ I(V,W;Z)` / `R1+R2 ≤ I(U,W;Y)+I(V;Z\|U,W)` / `R1+R2 ≤ I(V,W;Z)+I(U;Y\|V,W)` |
| ⭐ **[egk4] の等式** | **2 レート、しかも `=`** | `egk4.txt:10475-10480` 「In [?], it is shown that the above outer bound with no common message, i.e., **R0 = 0, is equal to the simpler region** consisting of all (R1, R2) such that `R1 ≤ I(U1; Y1)`, `R2 ≤ I(U2; Y2)`, `R1 + R2 ≤ min{I(U1; Y1) + I(X; Y2 \|U1), I(U2; Y2) + I(X; Y1 \|U2 )}` for some p(u1, u2, x)」⚠ **引用先は本 dump では `[?]` に潰れており未同定** |
| **[GK-outer] の J 族スライス実例** | **2 レート、ただし弱化** | `GK-outer.txt:273` Theorem 5「For any µ > 0 and for any TJ\|XY Z , any achievable rate **(0, R1 , R2 )** satisfies `R1 + µR2 ≤ max min …`」+ `GK-outer.txt:283-285` Proposition 1「For every TG,K\|XYZ , the outer bound in Theorem 3 implies the outer bound in Theorem 5 … **Proof. Letting R0 = 0**, and using (2d), (2g) and (2h), we obtain」 |

### 4.2 in-project の 2 レート資産はどの強度の対象か

⚠ **CLAUDE.md「textbook-object strength diff」の手順どおり、名前の強度修飾子と逐語の両方を見た**。

- **名前**: `bcOuterRegionUV` / `uvRegion` = **UV** であって **UVW ではない** (`rg -ni 'uvw' InformationTheory/` → **0 件**)。
  ⟹ 補助変数は 2 本 (`U`, `V`) で、文献の UVW 外界 (3 本) ではない。
- **逐語の制約スロット** (`OuterBoundUV/Bridge.lean:754-770`):
  `uvInfo₁ ν = mutualInfo ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.1)` = `I(V; Y₁)` /
  `uvInfo₂ ν = mutualInfo ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.2)` = `I(U; Y₂)` /
  `uvInfoSum₂ ν = uvInfo₂ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)` = `I(U;Y₂) + I(X;Y₁\|U)` /
  `uvInfoSum₁ ν = uvInfo₁ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.1)` = `I(V;Y₁) + I(X;Y₂\|V)`。
- ⟹ ⭐ **これは `egk4.txt:10477-10480` の "simpler region" の形と逐語で一致する**
  (条件付きスロットが**他方の補助変数ではなく入力 `X`**)。⟹ **in-project の 2 レート UV 資産は
  「弱い親戚」ではなく、教科書が `R₀=0` スライスと *等しい* と述べている当の対象である**。
  ⚠ **ただしその等式の一次出典は `[?]` に潰れており本 leg では同定していない** ⟹ 確信度は
  「教科書の断定を引いた」までであって、証明を読んだわけではない。
- ⚠ **`Thm7` にはこの diff が移らない** — [egk4] の記述は **UV/UVW 族**についてのものであり、
  J 族 (Theorem 7 / 8) の `R₀=0` スライスについて文献が持っているのは
  `GK-outer.txt:273` Theorem 5 = **加重和レートのスカラー上界 (上凹包つき)** という**さらに弱い対象**である。

### 4.3 ⚠ スライス側を採った場合の別債務 (⚠ 「従う」とも「従わない」とも書かない)

**債務そのもの**: **`R₀ = 0` スライスの effective compactness** — 3 レート版の実効コンパクト性から
2 レートスライスの実効コンパクト性が出るか。⚠ **これは領域の等式とは別の命題である**
(半計算可能性 = 片側の Π01 性は超平面との交わりで保たれるとは限らない)。

**債務を落とす候補は 2 つあり、どちらも本 leg では未着手である**:

1. **3 レート版から降ろす** — `Thm7(W) ∩ {R₀ = 0}` の被覆列を 3 レート版の被覆列から作る。
   ⚠ **「従う」と書いてはならない** (plan §7 判断ログ 2 / 前在庫 §2.5 末尾)。
2. **2 レート形の上で facts `## L2 (T3)` 行 6 の 6 段を直接回す** — この道は
   **2 レート形それ自身の基数境界**を要求する。UVW の 3 レート版には `GK-outer.txt:56-57` に
   境界があるが、**`egk4.txt:10477-10480` の 2 レート形の基数境界は本 leg では見つけていない**
   (`rg 'cardinality' egk4.txt` の BC 章のヒットは `:9780` / `:10372` の 2 件で、どちらも
   一般論の言及)。⟹ **候補 2 も無条件ではない**。

⟹ **N2 への渡し方**: 軸は「3 レート新設 vs 2 レートスライス」の 2 択のままだが、
**判断材料は 3 つ増えた** — (i) ゴールの主語は 2 レート (§4.1)、(ii) in-project の 2 レート UV 資産は
教科書の `R₀=0` スライスと**等しいと言われている**対象 (§4.2)、(iii) ただし **`Thm7` にはこの
橋が無く**、スライス側の実効コンパクト性は**2 通りともまだ開いている** (§4.3)。

---

## 5. 自前で置く要素 (優先度順) — ⚠ 何を分解したかを併記する

1. **(β) 実効性の層 1 枚** — §3.2 の分解 (β-1)〜(β-4)。⚠ **本体は (β-3)**
   (witness 空間の effective compactness)。近い実例は `isCompact_cornerSimplex` (**本体 14 行**、
   `Portfolio/Universal.lean:126-139`) だが、**それは古典的コンパクト性であって c.e. 性を含まない**
   ⟹ **14 行は下界ですらない**。⚠ **行数の単一の数値は出さない** — 出すなら
   「新規 def 3〜4 本 + 新規補題 (`REPred` の和・有限探索の閉包則) 3〜4 本 + (β-3) 1 定理」という
   分解の形で書くこと。⚠ **落とし穴** = (L-∀) を (L-∃) の双対と見ること
   (facts `## L2 (T3)` 行 6 の (L-∀) は **overtness** を使う別命題で、[AH] Prop 2.5 項目 2 とは違う)。
2. **(γ) 基数境界つきの領域 def** — `martonRegionUnionBounded` (`Marton/RegionCardinality.lean:270`) が
   唯一の先例。⚠ **落とし穴** = `closure` を付けたまま実効コンパクト性を主張すること
   (`bcOuterRegionUV_isClosed` の本体が `isClosed_closure` の 1 語であるのと同じ罠、§3.3)。
   ⚠ **`Thm7` の基数境界は `\|X\|+6` / `\|X\|+1` で `martonAuxBound α = Fintype.card α` とは別値**。
3. **(α) 13 変数の法則述語** — ⭐ **`iCondIndepFun` を使う** (§3.1、型検査済)。
   ⚠ **落とし穴** = `IsUVChannelLaw` を 13 変数へ一般化すること。
   **直接消費者 64 decl / 8 file、推移閉包 76 decl / 9 file** (`scripts/dep_consumers.sh` の実測)
   ⟹ **署名変更の波及がこの数**である。⚠ **新設なら 0**。
   ⚠ **落とし穴 2** = 対ごとの `IsMarkovChain` (`CondMutualInfo.lean:92`) の連言で済ませること
   (**3 分岐の相互独立は対ごとの条件付き独立から従わない**)。
4. **周囲空間の型の決定** (§4 = 前在庫 §2.5 の軸)。⚠ **落とし穴** = 一次文献 diff を取らずに選ぶこと
   ⟹ 本 leg が diff を取った (§4)。⚠ **決めるのは N2**。
5. **3 レート制約束 `(18a)`–`(18i)` の `min` 入り `structure`** — 前在庫 §9 T3 で elaborate 済。
   ⚠ **落とし穴** = 入れ子の向きを取り違えること (前在庫 §9 T4: **型検査は取り違えを守らない**)。

---

## 6. 前提の箱 — 事故になりやすい前提 (本 leg の新規分のみ。既出は前在庫 §4)

- **`iCondIndepFun` は `[StandardBorelSpace Ω]` を*周囲空間全体*に要求する**
  (`Conditional.lean:145` + 節変数 `:122`)。in-project の BC 家系は
  `[StandardBorelSpace α] [Nonempty α]` を**因子ごと**に宣言する形なので、13 タプルへの
  持ち上げが要る。⚠ **`Nonempty` は `iCondIndepFun` には要らないが `IsMarkovChain` には要る**
  (`CondMutualInfo.lean:92-95` の `[Nonempty X]` / `[Nonempty Y]`)。
- **`iCondIndepFun` の条件づけは確率変数ではなく部分 σ-加法族 `m'` + `hm' : m' ≤ mΩ`**。
  `X` で条件づけるには `MeasurableSpace.comap xProj inferInstance` と
  `(measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).comap_le` を渡す
  (実測、`n0_alpha.lean`)。⚠ **射影の合成の向きを間違えると `comap_le` が型不一致で落ちる** (実測で 1 度落ちた)。
- **`instCompactSpaceProbabilityMeasure` は `[MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]`
  の上で `[CompactSpace E]` から出る** (`Prokhorov.lean:65` + `:167`)。
  ⚠ **`E` に `ℕ` が 1 つでも混じると付かない** (P6 の実測) ⟹ **`bcOuterRegionUV` の添字型では使えない**。
- **`bcOuterRegionUV_isClosed` は実効コンパクト性の材料ではない** (本体 `isClosed_closure`)。
  ⚠ **署名だけ読んで「閉性は済んでいる」と数えない** (§4.2 規約 2 の実例)。
- **`martonRegionUnionBounded` は `[Fintype α]` を追加で要求する** (前在庫 §4 と同じ)。
  ⚠ 加えて `[Fintype β₁] [Fintype β₂]` も要る (`#check` 実出力)。
- **前在庫の `file:line` は 19 箇所を機械照合して全件生存**。⚠ **2 箇所だけ 1〜2 行ずれる** —
  `MartonFullSupport.lean:230` は `@[entry_point]` 行で decl は **`:231`**、
  `OuterBoundUV/Assembly.lean:850` は docstring 末尾で decl は **`:852`**。

---

## 7. Mathlib 壁の列挙

⚠ **本 leg で新たに立つ壁は 0 件**。前 relay の W1 / W3 は不変 (前在庫 §6 を参照。追認も再調査もしない)。
**W2 は射程を狭める方向に更新する** — 壁は残るが、**壁でない部分が確定した**。

| 不在のもの | 生クエリ (⚠ これだけを根拠にしない) | 結論形 / 実測による裏取り | 判定 |
|---|---|---|---|
| **W2′ 実効的な量化子補題 (L-∃) / (L-∀) と overtness の述語** | `REPred, IsCompact` → `Found 0 declarations mentioning REPred and IsCompact.` / `REPred, IsClosed` → `Found 0` / `Partrec, IsCompact` → `Found 0` | ⭐ **層の交差が空**: `Computable, TopologicalSpace` → **`Found 0`** / `Primcodable, TopologicalSpace` → **`Found 0`** / `Computable, Metric.ball` → **`Found 0`** / `TopologicalSpace.IsTopologicalBasis, Computable` → **`Found 0`**。`REPred` の全 API = **8 宣言**、うち生成則 4 本。in-project は `rg` で **0 decl** (`Computable\|Primrec\|Partrec\|REPred\|Primcodable` を含む 31 decl は全件 `Shannon/Kolmogorov/` のスカラー / `ℕ` / `List` 上)。**テンプレート**: 古典版は `isClosedMap_fst_of_compactSpace` (`Proper/Basic.lean:332`) と `isClosed_iInter` (`Topology/Basic.lean:147`) で**実際に通る** (P3 / P4 の実測) | **不在。⚠ ただし壁なのは「実効性の層 1 枚」だけ**で、古典版の連鎖・単体と確率測度空間のコンパクト性はすべて既存 |
| **W4 (新規) 実効コンパクト性を持つ in-project 領域** | (該当語彙が無いので生クエリ不能) | `rg 'IsCompact' InformationTheory/Shannon/BroadcastChannel/` → **0 件**。11 本の領域 def はすべて `closure (⋃ …)` で、`bcOuterRegionUV_isClosed` の本体は `isClosed_closure` の 1 語 | **不在。⚠ これは Mathlib の壁ではなく in-project の未着手**である ⟹ `@residual(wall:…)` の対象ではない |

⚠ **共有 sorry 補題は推奨しない** — W2′ は**定義 3〜4 本 + 補題数本**で書ける形であり
(前在庫 §8 のスケルトンが 2 レート版で型検査を通っているのと同じ理由)、`sorry` を共有すべき
「証明できない 1 命題」の形をしていない。⚠ **N2 が実装に入って (β-3) で詰まった場合に限り**、
そこで初めて `sorry` + `@residual(plan:bc-open-problem-t3c-plan)` を立てること。

---

## 8. 撤退ラインとの距離

- **§6-1 (N1 の gate が GO / NO-GO のどちらも返さない)** — 本 leg は触れない。**発火しない**。
  ⚠ **ただし N1 へ 1 点申し送りがある** (§9)。
- **§6-2 (N15 の棚卸しで層 3 に載る散文が 1 本も無い)** — 可変枠は未消化。**発火しない**。
- **§6-3 (20 leg 使い切り)** — 本 leg は N0 のみ。**発火しない**。
- **§6-4 (配分の撤退ライン)** — 本 leg の側は **`(C2)`** (gate)。§5.1 の数え方は **N3–N16 の行だけ**を
  数えるので、gate 2 本 (N0 / N1) はカウンタの入力に入らない。**発火しない**。
- **§6-5 (early gate の撤退ライン = N2 が返した員数が形式化枠 2 leg に収まらない)** —
  ⚠ **本 leg は員数を返す leg ではない** (それは N2)。**発火しない**。
  ⚠ **ただし本 leg の所見は §6-5 の判定に**両方向**に効く** — (α) は Mathlib に受け皿があり
  **軽くなる方向**、(β) は「実効性の層 1 枚」が丸ごと未着手で **重くなる方向**、
  (γ) は「領域 def は在るが実効コンパクト性の証拠を 1 つも運ばない」で **重くなる方向**である。
  ⚠ **どちらが勝つかは本 leg では測れない** (測るのが N2 である)。

**⚠ 新しい撤退ラインの提案はしない**。本 leg の結果は在庫の更新であって、退避が要る形の未達に当たらない。

---

## 9. N1 / N2 への申し送り (各 1 つだけ)

- **N1 へ**: ⭐ **11 種の `T_J` 適格性を回すなら `m15audit/aud.py` + `g67.py:50` を使うこと**。
  `m14/lib14.JKINDS` は **5 種** (`const/X/G/K/GK`) しか持たず、facts `## M19 (T3b)` M19-4 が
  要求する 11 種 (`const/X/X1/X2/Y1/Y2/Z1/Z2/Y/Z/GK`) を**見ない**。
  ⚠ **`aud.py` の限定は Theorem 8 側の `(31f)/(31g)` だけ**で、**Theorem 7 側は
  `(18a)`–`(18i)` + `(19)` + `(20)` + `(20c)` を完備している** (`aud.py:157-247`)。
- **N2 へ**: ⭐ **`bcOuterRegionUV_isClosed` を「閉性は済んでいる」と数えないこと**。
  本体は `isClosed_closure` の 1 語で、**def が `closure` だから閉じているだけ**である。
  ⟹ **11 本の in-project 領域はどれも実効コンパクト性の証拠を 1 つも運ばない**ので、
  員数を測るときの出発点は **0 本**であって 11 本ではない。

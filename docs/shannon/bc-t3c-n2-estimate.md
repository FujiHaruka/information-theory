# N2 — 形式化債務の員数 (early gate)

> **Parent plan**: [bc-open-problem-t3c-plan.md](bc-open-problem-t3c-plan.md)
> **入力の在庫 (⚠ 上書きしない。値は複製せず参照する)** =
> [bc-t3c-c2-inventory.md](bc-t3c-c2-inventory.md) / [bc-t3b-c2-inventory.md](bc-t3b-c2-inventory.md)
> 確定事実の SoT = [`bc-facts.md`](bc-facts.md) の `## L2 (T3)` 行 6 / `## M19 (T3b)` M19-5 /
> `## N1 (T3c)`。
>
> **leg 冒頭宣言 (N2)**: 側 = 形式化債務 / 動かすもの = §0 が要求する Lean proof done 側で最も重い段 (領域としての `Thm7(W)` / UV 外界の def と `∃p ∀T_J ∃aux` の量化子の段) の**員数を初めて測り**、残る形式化枠 2 leg (N17/N18) に収まるかを §6-5 の判定として返す

---

## 0. 一行サマリ

**軸の決定 = 3 レートで受け皿を新設する** (`R₀ = 0` スライスは派生 def として同時に置く。§1)。
**員数 = 新規 def 41 本 + 新規補題 4 本 + 中核定理 11 本** (§3)。
うち **def 41 本と補題 4 本は本 leg で実際に書いて `lake env lean` を通した** (probe 13 本、§4) が、
**中核定理 11 本は 1 本も証明していない**。**§6-5 の判定 = 収まらない** (§5)。
⚠ **ⓓ (壁) は 0 件である** — 詰まっているのは「書けない」ではなく「量」であり、
**これを「残るのは行数と配線だけ」と読んではならない** (中核 11 本のうち 7 本は Mathlib に
計算可能解析の層が 1 宣言も無い側にある。§2 (β) 行 / §3.2 の 1–7)。

⭐ **最も危険な所見**: facts `## L2 (T3)` 行 6 の段 (1) が「相互情報量は単体上連続かつ**計算可能**」と
1 語で置いている部分は、Lean では**独立した中核定理 2 本**である (実効連続性 + 制約集合の Π01 性)。
`Computable` は `Primcodable` 型の上にしか無く `Primcodable ℝ` は存在しないので、
**有理近似の層を先に作らないと言明すらできない**。⚠ 本 leg は言明できる形まで作って型検査を通した
(`n2_beta.lean`) ので、これは**壁ではなく自前実装**である。

---

## 1. 設計軸の決定

### 1.1 決定

⭐ **3 レートで受け皿を新設する** (`thm7Region : … → Set (ℝ × ℝ × ℝ)`)。
**`R₀ = 0` スライスは捨てず、派生 def として同時に置く** (`thm7RegionSlice`、実測で 2 行)。

### 1.2 理由 (4 本、うち 3 本は機械/逐語で裏を取った)

1. **一次文献の主語が 3 レート**で、**基数境界も実効コンパクト性の 6 段も 3 レート形で書かれている**
   (在庫 §4.1 の逐語 / facts `## L2 (T3)` 行 6)。形式化が散文と 1:1 に対応する。
2. **J 族には 2 レート版の「領域」が文献に無い**。最も近いのは在庫 §4.1 が引く GK-outer Theorem 5 =
   **加重和レートのスカラー上界** (上凹包つき) で、**厳密に弱い親戚**である
   ⟹ CLAUDE.md「textbook-object strength diff」の赤信号にそのまま当たる。
3. **既存 2 レート資産に載せても実効コンパクト性の証拠は 1 つも引き継げない** (在庫 §3.3 / §9 —
   11 本すべて `closure (⋃ …)`)。⟹ 「既存資産に載せる」の利得は**周囲空間の型だけ**である。
4. **3 レートで置けばスライスは 2 行で取れるが、逆は取れない** (実測: `n2_b.lean` の
   `thm7RegionSlice` + `slice_comm`)。

### 1.3 決めた側の債務 (3 件、すべて機械で裏を取った)

| # | 債務 | 裏取り |
|---|---|---|
| **D1** | **3 レートの周囲空間の汎用補題が 1 本も無い** — 下方集合性・非空性・閉性を 1 本ずつ書き直す | `rg -c 'Set \(ℝ × ℝ × ℝ\)' InformationTheory/` → **0** (本 leg で再導出) |
| **D2** | **`Thm7 ⊇ C` を 3 レートで述べるには 3 レートの operational 容量領域の新設が要る** | `#check` 実出力: `BCAchievable : … → BCChannel α β₁ β₂ → ℝ → ℝ → Prop` / `bcCapacityRegion : … → Set (ℝ × ℝ)` (`n2_sig.lean`) ⟹ **既存は 2 レート** |
| **D3** | **領域 def に `[TopologicalSpace α] [DiscreteTopology α] [BorelSpace α]` の 3 つが追加で要る** | `n2_a3.lean` A3 が通り `n2_a3_neg.lean` A4 が**逐語で落ちた** (§4)。BC 家系の既存署名には `[TopologicalSpace` **0 件** / `DiscreteTopology` **0 件** / 素の `BorelSpace` **0 件** (本 leg で再導出) |

### 1.4 決めなかった側 (`R₀ = 0` スライス) で回避できた債務

- **D1 と D2 は回避できた** — 既存の 2 レート平面 `Set (ℝ × ℝ)` にそのまま載るので、
  汎用補題の再実装も operational 側の新設も要らなかった。**D3 は回避できない** (スライス側でも
  `ProbabilityMeasure` のコンパクト性を使う以上、同じ 3 つの型クラスが要る)。
- ⚠ **「`R₀=0` なら `W`/`Ŵ`/`W̃` の 3 本を落とせる」は緩める方向の見立てで、逐語で潰れた** —
  `(18b)` の右辺は `R₀ = 0` を代入しても `min{I(W;Y), I(W;Z)} + I(U;Y|W)` のままである
  (在庫 §4.1 が引く `auxrec.txt:1038`)。⟹ **補助変数は 9 本のまま**で、スライス側の利得ではない。

### 1.5 ⚠ 未決のまま持つもの

**`R₀ = 0` スライスの effective compactness**。本 leg が測ったのは
**集合レベルの可換性 1 本だけ**である — `slice_comm` (`n2_b.lean`、証明つきで通った) は
「スライスは `⋃` とも `⋂` とも可換」を言うが、**Π01 性が保たれるかは 1 行も測っていない**。
⚠ **在庫 §4.3 の候補 2 つはどちらも開いたままである**。⚠ **これは緩める方向の見立てなので、
§4.5 の 3 つの道具のどれで殺すかを決めるまで leg の主戦力に据えない** (親 plan §4.4 処方 2)。

---

## 2. 段の分解表

**facts `## L2 (T3)` 行 6 の 6 段**を左から 2 列目に対応させる (段番号はその行の (1)–(6))。
分類は ⓐ 既存で足りる / ⓑ 配線 / ⓒ 自前実装 / ⓓ 壁。

| # | 段 | 行 6 の段 | 分類 | 既存資産の逐語署名 (`#check` 実出力) | probe | ⚠ 通った probe が保証していないこと |
|---|---|---|---|---|---|---|
| **a-1** | `Thm7(W)` の 1 法則分の制約束 `(18a)`–`(18i)` (`min` 入り) を領域として返す def | 段 (1) | **ⓒ** | — (自前。**実スロット 17 本**) | `n2_a1` / `n2_b` **通** | 制約の**転記が正しいこと**を保証しない (型は 17 本の `ℝ` を区別しない) |
| **c** | 適格性 `(19a)`–`(19c)` / `(20a)` / `(20b)` / `(20c)` の完全形 | 段 (1) | **ⓒ** | — (自前。**追加スロット 8 本** ⟹ 合計 **25 スロット**) | `n2_a1` `Thm7Eligible` **通** | 同上。`(19)` の左右の符号取り違えを守らない |
| **a-1′** | 17 スロットを 13 タプル上の相互情報量として読み出す | 段 (1) | **ⓑ** | `@InformationTheory.Shannon.mutualInfo : {Ω} → [MeasurableSpace Ω] → {X} → [MeasurableSpace X] → {Y} → [MeasurableSpace Y] → Measure Ω → (Ω → X) → (Ω → Y) → ENNReal` / `@InformationTheory.Shannon.condMutualInfo : {Ω} → [MeasurableSpace Ω] → {X} → [MeasurableSpace X] → {Y} → [MeasurableSpace Y] → {Z} → [MeasurableSpace Z] → (μ : Measure Ω) → [IsFiniteMeasure μ] → [StandardBorelSpace X] → [Nonempty X] → [StandardBorelSpace Y] → [Nonempty Y] → (Ω → X) → (Ω → Y) → (Ω → Z) → ENNReal` | `n2_a2` **通** (17/17) | **どの射影がどの変数か**を保証しない。⚠ `ℝ≥0∞` なので差は切断減算 ⟹ `.toReal` が必須 |
| **a-2** | 基数境界つきの `⋃` (9 補助 × `\|X\|+6` / `\|X\|+1`) | 段 (2) | **ⓑ** | 先例 = `Marton.martonRegionUnionBounded` (在庫 §3.3 に逐語) | `n2_b` **通** (⚠ **1 度落ちた**、§4) | 上限値が `Thm7` のものであることを保証しない (`martonAuxBound α = Fintype.card α` とは別値) |
| **a-3** | `closure` を付けずに閉性を出す (1 法則分) | 段 (6) の前段 | **ⓒ** | — (自前。`isClosed_le` × 9 + `ext` の橋 = **35 行**) | `n2_a1` `isClosed_thm7RegionOfInfo` **通** | 合併レベルの閉性を**まったく**保証しない |
| **a-3′** | 同 (合併レベル) | 段 (6) の前段 | **ⓑ+ⓒ** | `@isClosedMap_fst_of_compactSpace : ∀ {X Y} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y], IsClosedMap Prod.fst` (`Mathlib/Topology/Maps/Proper/Basic.lean:332`) / `@isClosed_iUnion_of_finite : ∀ {X ι} [TopologicalSpace X] [Finite ι] {s : ι → Set X}, (∀ i, IsClosed (s i)) → IsClosed (⋃ i, s i)` (`Mathlib/Topology/Basic.lean:181`) / `@Set.Finite.isClosed_biUnion : ∀ {X α} [TopologicalSpace X] {s : Set α} {f : α → Set X}, s.Finite → (∀ i ∈ s, IsClosed (f i)) → IsClosed (⋃ i ∈ s, f i)` (`Mathlib/Topology/Basic.lean:171`) | `n2_a3` template **通** / `n2_a3_neg` B2 **落** | template は**同時閉性** `IsClosed {q \| q.1 ∈ S q.2}` を仮定に持つ ⟹ **各ファイバの閉性だけでは足りない** (B2 が逐語で落ちた) |
| **b-1** | `∃p` の段 | 段 **(5)** | **ⓑ** | `⋃ (p : ProbabilityMeasure α)` | `n2_b` **通** | `p` が `ν` の `X` 周辺法則と一致することは**法則述語の側**で言う必要がある |
| **b-2** | `∀T_J` の段 | 段 **(3) + (4)** | **ⓑ** | `⋂ (kJ) (TJ : Kernel (α × β₁ × β₂) (bcAux kJ)) (_ : IsMarkovKernel TJ)` | `n2_b` **通** / `n2_stages` **通** | ⚠ 定義側では `⋂ (kJ) (TJ)` に潰れているが、**Π01 の証明では段 (3) と段 (4) は別段**である (段 3 は一様性、段 4 は c.e. 添字上の可算和)。`n2_stages` は**集合として同じ**ことだけを `rfl` で確認 |
| **b-3** | `∃aux` の段 | 段 **(2)** | **ⓑ** | 上の a-2 と同じ `⋃` | `n2_b` **通** | 入れ子の**向き**を保証しない (前在庫 §9 T4: 両向きとも elaborate する) |
| **α** | 13 変数の法則述語 (4 節) | 段 (1) の前提 | **ⓑ + ⓒ** | `ProbabilityTheory.iCondIndepFun` (逐語署名は在庫 §3.1) | `n2_alpha` **通** (4 節すべて) | ⚠ **4 節の連言が `auxrec.txt:1074` の因子分解と同値であることを 1 行も示していない** (在庫 §3.1 の債務 1 がそのまま残る) |
| **β-0** | 相互情報量の実効連続性 / 制約集合の Π01 性 | 段 **(1)** | **ⓒ** | ⚠ **無い**。loogle: `Computable, Real` → `Found 0` / `Computable, Real.log` → `Found 0` / `Computable, MeasureTheory.Measure` → `Found 0` / `Primcodable, Real` → `Found 0` / `ComputablePred, Real` → `Found 0`。結論形 `\|- Computable _` は **43 件 match** だが**全件が離散層** (`Primcodable ℝ` が無いため) | `n2_beta` **言明のみ通** | **証明を 1 行も含まない** |
| **β-1/2** | 有理球と `Primcodable` の道具 | 段 (1)(2) | **ⓐ** | `@REPred : {α} → [Primcodable α] → (α → Prop) → Prop` / `@Primcodable.finArrow : {α} → [Primcodable α] → {n : ℕ} → Primcodable (Fin n → α)` | `n2_beta` **通** (`Primcodable (RatBallN n)` / `Primcodable (List (RatBallN n))` が全次元で合成) | 何も証明していない (instance の存在のみ) |
| **β-3** | witness 空間 (単体の直積) の実効コンパクト性 | 段 **(2)** | **ⓒ** ⭐**本体** | 古典側のみ既存: `isCompact_stdSimplex : ∀ (𝕜 ι) [Fintype ι] [TopologicalSpace 𝕜] [Semiring 𝕜] [PartialOrder 𝕜] [OrderClosedTopology 𝕜] [ContinuousAdd 𝕜] [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜], IsCompact (stdSimplex 𝕜 ι)` | `n2_beta` **言明のみ通** | c.e. 性を 1 行も含まない |
| **β-4** | (L-∃) の実効版 | 段 **(2)(5)** | **ⓒ** | 古典版のみ: `isClosedMap_fst_of_compactSpace` (上) | `n2_beta` `LExists` **言明のみ通** | 同上 |
| **β-4′** | (L-∀) の実効版 + overtness の述語 | 段 **(3)** | **ⓒ** | 古典版のみ: `@isClosed_iInter : ∀ {X ι} [TopologicalSpace X] {f : ι → Set X}, (∀ i, IsClosed (f i)) → IsClosed (⋂ i, f i)` (`Mathlib/Topology/Basic.lean:147`) | `n2_beta` `LForall` / `IsComputablyOvertN` **言明のみ通** | ⚠ **(L-∀) を (L-∃) の双対と見ない** — overtness は別述語で、古典版には対応物が無い (古典 (L-∀) は `Y` に何の仮定も要らない) |
| **β-5** | 一様 Π01 の可算共通部分閉包 | 段 **(4)** | **ⓒ** | — | `n2_beta` `Pi01ClosedUnderIInterUniform` **言明のみ通** | ⚠ 一様でない版 (`Pi01ClosedUnderIInter`) も書けてしまう ⟹ **型は一様性の脱落を守らない** |
| **γ** | `ProbabilityMeasure` 添字のコンパクト性 | 段 (2)(5) | **ⓐ** (⚠ 型クラス 3 個追加) | `instance [CompactSpace E] : CompactSpace (ProbabilityMeasure E)` (`Mathlib/MeasureTheory/Measure/Prokhorov.lean:167`、節変数 `{E : Type*} [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]` = 同 `:65`) | `n2_a3` A1/A2/A3 **通** / `n2_a3_neg` A4 **落** | ⚠ **既存 BC 家系の型クラス列 (`[Fintype α] [MeasurableSpace α]`) では付かない** (A4 の逐語エラー) |
| **δ** | 3 レート operational 容量領域と 2 レート `bcCapacityRegion` の接続 | — (接続) | **ⓒ** | — | **未測定** | — |

⚠ **ⓓ (壁) は 0 件**。「無い」ものはあるが、すべて既存部品で**言明でき**、
`n2_beta.lean` が型検査で示している ⟹ `@residual(wall:…)` の対象ではない。
⚠ **共有 sorry 補題も推奨しない** — 「証明できない 1 命題」の形をしていない (在庫 §7 と同じ理由)。

---

## 3. 員数

### 3.1 分解形の総計

| 種別 | 本数 | 内訳 | 状態 |
|---|---|---|---|
| **新規 def / abbrev / structure / instance** | **41** | (γ) 領域層 **30** (`n2_b.lean`: 13 射影 + `Amb` + `bcAux` + `InThm7Region` + `thm7OneLaw` + `tripleType` + その `MeasurableSpace` instance + `auxTriple` + `mX` + `ChannelClause` + `JClause` + `IsThm7LawShape` + `thm7OneLawP` + `IsThm7LawShapeP` + `thm7BoundW` + `thm7BoundU` + `thm7Region` + `thm7RegionSlice`) / (a-1)(c) の追加 **3** (`Thm7Info` / `thm7RegionOfInfo` / `Thm7Eligible`) / (β) 語彙 **8** (`RatBallN` / `ratBallNSet` / `IsEffectivelyCompactN` / `IsEffectivelyOpenN` / `IsEffectivelyClosedN` / `IsComputablyOvertN` / `joinFin` / `IsEffectivelyContinuousN`) | ⭐ **41/41 が本 leg で型検査を通った** |
| **新規補題 (証明つき)** | **4** | `mX_le` / `slice_comm` / `isClosed_thm7RegionOfInfo` / `isClosed_iUnion_of_compactSpace` | ⭐ **4/4 が通った** |
| **中核定理 (未証明)** | **11** | §3.2 | ⚠ **0/11**。1 本も証明していない |

### 3.2 中核定理 11 本 (優先度順)

| # | 定理 | 段 | 分類 | ⚠ 落とし穴 |
|---|---|---|---|---|
| 1 | 相互情報量汎関数の**実効連続性** (`MutualInfoEffectivelyContinuous`) | (1) | ⓒ | Mathlib に計算可能解析の層が **0 宣言** ⟹ 有理近似を自前で組む |
| 2 | 制約集合の **Π01 性** (`ConstraintSetPi01`) | (1) | ⓒ | 1 に依存。⚠ **非狭義**不等式であることが本質 (狭義だと開集合になる) |
| 3 | witness 空間の**実効コンパクト性** (`WitnessEffectivelyCompact`) | (2) | ⓒ ⭐**本体** | 古典側 `isCompact_stdSimplex` は c.e. 性を 1 行も含まない |
| 4 | **(L-∃)** の実効版 (`LExists`) | (2)(5) | ⓒ | 3 に依存 |
| 5 | witness 空間の **overtness** (`IsComputablyOvertN 𝒯_k`) | (3) | ⓒ | 3 とは**別の片側性** |
| 6 | **(L-∀)** の実効版 (`LForall`) | (3) | ⓒ | 5 に依存。⚠ **4 の双対ではない** |
| 7 | 一様 Π01 の**可算共通部分閉包** (`Pi01ClosedUnderIInterUniform`) | (4) | ⓒ | 一様性を落とすと言明が弱くなる (型は守らない) |
| 8 | `IsClosed (thm7Region W)` を **`closure` なしで** (合併レベル) | (6) 前段 | ⓑ+ⓒ | 各ファイバの閉性では足りない (`n2_a3_neg` B2) |
| 9 | `thm7Region W ⊆ [0, log\|X\|]³` (有界性) | (6) | ⓒ | 相互情報量の上界を 17 スロット分 |
| 10 | (α) **合致の証明** — 4 節の連言 ⟺ `auxrec.txt:1074` の因子分解 | (1) 前提 | ⓒ | 在庫 §3.1 の債務 1。⚠ **「従う」と書かない** |
| 11 | 3 レート operational 容量領域の新設 + `bcCapacityRegion` との接続 | — | ⓒ | D2。⚠ **本 leg では 1 行も測っていない** |

### 3.3 行数について

**本 leg で実際に書いて型検査を通した受け皿の生行数 = 629 行**
(`n2_a1` 144 + `n2_alpha` 120 + `n2_b` 191 + `n2_beta` 133 + `n2_a3` 41)。
⚠ **これは docstring / 命名規約 / style gate を通す前の生の行数**であり、in-project へ移すと増える。
⚠ **中核定理 11 本の行数は 1 行も測れていない** — 1 本も証明していないからである。
近い実例は `isCompact_cornerSimplex` (本体 14 行、在庫 §5-1 が SoT) だが、
**それは古典的コンパクト性であって c.e. 性を 1 行も含まない** ⟹ **下界ですらない**。

### 3.4 ⚠ 見立ての向き (親 plan §4.4)

**締める方向 (義務を追加する) 5 件 — 着手前に機械へ掛けた結果、2 件が覆り 3 件が残った**:

| # | 見立て | 機械の答え |
|---|---|---|
| 1 | 「13 タプルに `StandardBorelSpace` が付かない」 | ⭐ **覆った** — `n2_sbs3` (i) 予算を上げれば通る / (ii)(iii) 手組み `have` 11 行でも通る ⟹ **ⓑ 配線** |
| 2 | 「10 添字の合併は elaborate しない」 | ⭐ **覆った** — `n2_b2` の V1/V2 は**既定予算 3.5 秒**で通る ⟹ 真因は `(ν : Measure _)` の下線であって合併ではない |
| 3 | 「領域 def に `[TopologicalSpace α] [DiscreteTopology α] [BorelSpace α]` が要る」 | **覆らなかった** — `n2_a3_neg` A4 が逐語で落ちた |
| 4 | 「(L-∀) は (L-∃) の双対ではない (別述語 1 本が要る)」 | **覆らなかった** — 古典版は `Y` に仮定を要求しない (`n2_beta` の古典 (L-∀)) のに実効版は overtness を要求する ⟹ 対応物が無い |
| 5 | 「相互情報量の実効連続性が独立した段として要る」 | **覆らなかった** — loogle 5 クエリ全 `Found 0` + 結論形 43 件全件が離散層 |

⚠⚠ **前 relay の「締める方向は 9/9 で覆る」較正は本 leg で再現しなかった (5 件中 2 件)**。
**母集団が違う** — 前 relay の母集団 B は数値・恒等式の見立て、本 leg は型検査と Mathlib 在庫の
見立てである。⟹ **同じ較正を持ち込んではならない**。

**緩める方向 (義務を減らす) 3 件 — 3 件とも採らなかった**:

| # | 見立て | どう殺したか (§4.5 の道具) |
|---|---|---|
| 1 | 「`R₀=0` なら `W`/`Ŵ`/`W̃` の 3 本が落ちる」 | **逐語** — `(18b)` は `R₀=0` でも `W` を含む ⟹ **潰れた** |
| 2 | 「スライスが `⋃`/`⋂` と可換だから Π01 も保たれる」 | **恒等式への帰着** — 集合レベルは `slice_comm` で確定したが **Π01 側は 1 行も測っていない** ⟹ **採らない** |
| 3 | 「既存 2 レート資産に載せれば実効コンパクト性が引き継げる」 | 在庫 §3.3 で既に潰れている (11 本すべて `closure`) |

---

## 4. 型検査 probe の一覧 (実測)

置き場所 = `$SP/n2/` (`SP` の逐語は親 plan §4.9)。⚠ **`InformationTheory/` へは 1 行も書いていない**。
**13 ファイル / 1017 行**。

| # | ファイル | 行 | 試した主張 | 結果 |
|---|---|---|---|---|
| P1 | `n2_a1.lean` | 144 | `(18a)`–`(18i)` の完全形 (入れ子 `min` つき、**17 スロット**) + `(19)`/`(20)` (**+8 スロット**) + 領域 def + **1 法則分の閉性を `closure` なしで** | ✅ **通** (閉性の本体 = `ext` の橋 19 行 + `isClosed_le` 9 本) |
| P1a | 同 | — | `structure Thm7Info` のフィールドを `iWY iWhY iWZ iWtZ : ℝ` とまとめ書き | ❌ **落**: `error(lean.inferBinderTypeFailed): Failed to infer type of binder ` + `invalid field notation: … The expression I has type Thm7Info which does not have the necessary form` ⟹ **structure のフィールドは 1 行 1 本** |
| P2 | `n2_a2.lean` | 90 | 13 タプル上で **17 スロット全部**を `mutualInfo` / `condMutualInfo` で読み出す (対で条件づける 2 本を含む) | ✅ **通** (17/17)。⚠ 保証しないもの = **射影と変数の対応** |
| P3 | `n2_alpha.lean` | 120 | (α) **4 節すべて** — 異なる型の 3 補助三つ組の `iCondIndepFun` + `ChannelClause` + `JClause` + 周辺法則の連言、および対ごとの取り出し | ✅ **通**。⚠ 保証しないもの = **逐語の因子分解との同値** |
| P4 | `n2_sbs.lean` | 40 | `StandardBorelSpace` が 13 タプルに付くか | ❌ **S5 / S6 が落**: `failed to synthesize instance of type class StandardBorelSpace (bcAux k1 × … × bcAux k9)` (S1–S4 は通る) |
| P5 | `n2_sbs2.lean` | 54 | 同・**どこで止まるか** | ❌ **5 因子以上が全滅** (4 因子までは通る)。⚠ 副産物: **docstring の直後に `set_option … in` は書けない** (`unexpected token 'set_option'; expected 'lemma'`) |
| P6 | `n2_sbs3.lean` | 59 | 同・**予算を上げる / 手組みで繋ぐ** | ✅ **両方通** — `synthInstance.maxSize 2000` + `maxHeartbeats 4000000` で 5 因子が通り、手組み `have` 11 行で 13 タプルも通る ⟹ ⭐ **これは配線であって壁ではない** |
| P7 | `n2_b.lean` (初版) | — | 10 添字の合併 + `(ν : Measure _)` の下線 | ❌ **落**: `(deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached` → 2000000 に上げても**同じ箇所で落ちた** (2 分 15 秒) |
| P8 | `n2_b2.lean` | 85 | 同・**真因の切り分け** (V1 = 法則なし / V2 = 周囲空間を明示 + `IsProbabilityMeasure` 束縛子) | ✅ **両方が既定予算 3.5 秒で通** ⟹ 真因は**下線の周囲空間**であって合併ではない |
| P9 | `n2_b.lean` (最終) | 191 | ⭐ **領域 `Thm7(W)` を端から端まで** — `⋃_p ⋂_{T_J} ⋃_{aux}` / `\|X\|+6` と `\|X\|+1` の基数境界 / 13 タプル / 17 スロット / 4 節の法則 / `R₀=0` スライス / `slice_comm` | ✅ **通** (**既定予算 5.2 秒、0 sorry**)。⚠ 保証しないもの = **入れ子の向き** (前在庫 §9 T4) / **射影と変数の対応** / **上限値が `Thm7` のものであること**。⚠ **実効コンパクト性は 1 行も出していない** |
| P10 | `n2_a3.lean` | 41 | (a-3′) 合併レベルの閉性 template (同時閉性 + コンパクト添字) / `isClosed_iInter` / `ProbabilityMeasure` のコンパクト性 3 通り | ✅ **通** (template の本体は **6 行**) |
| P11 | `n2_a3_neg.lean` | 20 | **通ってはならない 2 本** | ❌ **2 本とも期待どおり落** — A4: `failed to synthesize instance of type class TopologicalSpace (ProbabilityMeasure α)` (α が `[Fintype α] [MeasurableSpace α]` だけのとき) / B2: `failed to synthesize instance of type class AlexandrovDiscrete X` (`isClosed_iUnion` は別物) |
| P12 | `n2_beta.lean` | 133 | (β) 次元つきの実効性層 — `IsEffectivelyCompactN` / `IsEffectivelyOpenN` / `IsEffectivelyClosedN` / `IsComputablyOvertN` / `IsEffectivelyContinuousN` / (L-∃) / (L-∀) / 一様 Π01 の ⋂ 閉包 / 制約集合の Π01 性、+ 古典側の対照 3 本 | ✅ **全部通** (⚠ **言明のみ。証明は 1 本も無い**) |
| P13 | `n2_stages.lean` | 13 | `⋂ (i) (t), S i t = ⋂ i, ⋂ t, S i t` | ✅ **`rfl` で通** ⟹ 段 (3)/(4) の分割は**証明側の帳簿**であって定義側の分岐ではない |
| S | `n2_sig.lean` | 27 | 引用する全資産の逐語署名を `#check` で取得 | ✅ **通** |

⚠ **落ちた 4 件が最も情報量が高い** — P1a (syntax) / P4・P5 (instance 探索の予算) / P7 (下線の周囲空間) /
P11 (追加の型クラス 3 個と、ファイバごとの閉性では足りないこと)。**うち 3 件は P6 / P8 で覆った**。

---

## 5. §6-5 の判定

### 5.1 判定 = ⚠ **収まらない**

**根拠 (§3 の分解に紐付ける)**:

- **受け皿 (def 41 + 補題 4) は 629 行で型検査を通っており、N17 の 1 leg に収まる公算が高い**。
  ⚠ ただし docstring / 命名規約 / style gate / honesty gate を通す分が上乗せになる。
- **中核定理 11 本が収まらない**。とくに **1–7 の 7 本は Mathlib の計算可能解析の層そのものであり、
  BC とは独立した一般命題である** (loogle 5 クエリ全 `Found 0`、結論形 43 件全件が離散層)。
  **1 leg で 7 本の中核定理を証明する見込みは無い**。
- ⚠ **これは「壁だから届かない」ではない** — ⓓ は 0 件で、すべて言明できている (§2)。
  **「量が 2 leg に収まらない」という事実**である。CLAUDE.md の語彙では **big であって blocked ではない**。
- ⚠ **これは `GOAL-CHANGE` ではない** — §0 は動かさない。「届かない」という事実を書くだけである。

### 5.2 切り出す単位の提案 (3 個)

⚠ **可変枠 N3–N16 に吸わせる案は書かない** (§5.2-1)。

| # | 単位 | 中身 | 依存 | なぜこの粒度か |
|---|---|---|---|---|
| **A** | **計算可能解析の層** (仮の filename stem: `bc-effective-compactness-plan`) | §3.2 の中核 **1–7** (実効連続性 / 制約集合の Π01 / witness 空間の実効コンパクト性 / (L-∃) / overtness / (L-∀) / 一様 Π01 の ⋂ 閉包) + (β) 語彙 8 def | **BC から独立** | ⭐ **BC の対象を 1 つも含まない一般命題の束**であり、Mathlib へ出せる形をしている。BC 側の設計変更に巻き込まれない |
| **B** | **3 レート `Thm7(W)` の領域層** (仮: `bc-thm7-region-plan`) | §3.1 の def 41 のうち (γ) 領域層 30 + (a-1)(c) の 3 + 補題 4 + §3.2 の中核 **8–10** | A に依存しない (閉性は古典側で閉じる) | ⭐ **本 leg で 629 行が型検査を通っている** ⟹ **type-check done まで最短**。A の完成を待たずに着地できる |
| **C** | **3 レート operational との接続** (仮: `bc-three-rate-operational-plan`) | §3.2 の中核 **11** + D2 | B に依存 | ⚠ **本 leg では 1 行も測っていない** ⟹ 員数不明のまま切り出す。**B の着地後に N2 相当の測定をやり直す**こと |

⚠ **参照は `@residual(plan:<新 plan の filename stem>)` で行う** (親 plan §6-5)。

### 5.3 ⚠ 「収まる」と判定した場合の義務について

本 leg の判定は **収まらない** なので §4.1 軸 2 の「N17 着手*後*に残りの段の在庫を取り直す」義務は
**この形では発火しない**。⚠ **ただし切り出し先 B に着手した後は同じ義務が立つ** — 単位 C の員数は
本 leg では**未測定**だからである (§5.2 の C 行)。

---

## 6. 前提の箱 — 事故になりやすい前提 (⚠ 本 leg の新規分のみ。既出は在庫 §6)

- **`StandardBorelSpace` は右入れ子の積で 5 因子目から既定予算では合成できない** (P4/P5 実測)。
  ⚠ **「付かない」と読むと壁を 1 件でっち上げることになる** — `synthInstance.maxSize` を上げるか
  手組み `have` 11 行で通る (P6)。⟹ **配線**。
- **`ProbabilityMeasure` の束縛子の下で `(ν : Measure _)` と下線を書くと、10 添字の合併の中では
  elaborate が終わらない** (P7、2000000 heartbeats でも落ちる)。⚠ **合併の大きさのせいだと読むと
  設計を誤る** — 周囲空間を明示するか、**係数を合併の外で解決する `def` を 1 本挟む**と
  既定予算 5 秒で通る (P8/P9)。
- **`condMutualInfo` は第 1・第 2 引数に `[StandardBorelSpace] [Nonempty]` を要求する**
  (逐語署名は §2 の a-1′ 行)。⟹ **9 補助 + `α` + `β₁` + `β₂` + `J` の 13 型すべてに要る**。
  ⚠ `Fintype` からは自動では出ない。
- **`mutualInfo` / `condMutualInfo` は `ℝ≥0∞` を返す**。`(18c)` などの**差**は切断減算になるので
  **`.toReal` を挟まないと制約の意味が変わる** (既存 `uvRegion` と同じ作法)。
- **`ProbabilityMeasure α` のコンパクト性には `[TopologicalSpace α] [DiscreteTopology α]
  [BorelSpace α]` が要る** (`Prokhorov.lean:65` + `:167`、P10/P11 実測)。
  ⚠ **BC 家系の既存署名にはこの 3 つが 1 件も無い** ⟹ **領域 def の型クラス列が既存 11 本と揃わない**。
- **`isClosed_iUnion` は `[AlexandrovDiscrete X]` を要求する別物である** (P11 の逐語)。
  ⚠ **名前で選ぶと落ちる** — 要るのは `isClosedMap_fst_of_compactSpace` か
  `isClosed_iUnion_of_finite` / `Set.Finite.isClosed_biUnion` である。
- **`structure` のフィールドはまとめ書きできない** (P1a)。⚠ 25 スロットを書くときに 1 度落ちる。
- **docstring の直後に `set_option … in` は書けない** (P5 の副産物)。

---

## 7. N17 / N18 への申し送り (各 1 つだけ)

- **N17 へ**: ⭐ **`$SP/n2/n2_b.lean` (191 行) をそのまま出発点にすること**。
  領域 `Thm7(W)` は `⋃_p ⋂_{T_J} ⋃_{aux}` / 基数境界 / 13 タプル / 17 スロット / 4 節の法則まで
  **既定予算 5.2 秒・0 sorry で通っている**。⚠ **ただし `(ν : Measure _)` の下線を 1 つ戻すだけで
  elaborate が終わらなくなる** (P7) ので、`thm7OneLawP` / `IsThm7LawShapeP` の**係数を合併の外で
  解決する 2 本を消さないこと**。
- **N18 へ**: ⚠ **`n2_beta.lean` の 7 本の `Prop` 値 def を「定義できたから段が軽い」と読まないこと**。
  **7 本とも証明を 1 行も含まない**。⚠ とくに **(L-∀) を (L-∃) の双対として書き始めない** —
  古典版 (L-∀) は `Y` に何の仮定も要求しないのに、実効版は **overtness という別の片側性**を
  要求する (§2 の β-4′ 行)。**先に `IsComputablyOvertN` を単体で決着させること**。

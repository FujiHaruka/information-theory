# Ch.14 Kolmogorov 複雑性 第 2 波 (prefix 塔) ムーンショット計画 🌙

> **Sibling moonshot**: [`kolmogorov-moonshot-plan.md`](kolmogorov-moonshot-plan.md)
> (第 1 波 = plain C 背骨、P1–P6 全 proof-done)。第 2 波は第 1 波の `complexity`/`condComplexity`/
> `invariance`/`incompressible_count` を read-only 消費し、その上に prefix 複雑性 K の塔を載せる。
> 第 1 波 §Out がここへの backlink を持つ (親子ではなく兄弟 moonshot 関係)。

> **SoT**: 山場マップ = [`kolmogorov-scouting.md`](kolmogorov-scouting.md) §0/§1/§3、per-lemma 台帳 =
> [`kolmogorov-w2-inventory.md`](kolmogorov-w2-inventory.md) (**最重要**、Kraft 既存の overturn + Key-preconditions box)。
> 本計画は両者を実装 Phase に落とす制御文書。壁断定・settled fact はここに散文で書かず slug / 再検証コマンドで参照する。

## 進捗 (DAG)

- [x] Phase M0 — Mathlib API 在庫調査 ✅ → [`kolmogorov-w2-inventory.md`](kolmogorov-w2-inventory.md)
- [ ] Gateway atom — prefix-free 機械 U_pf + K + P_U + Kraft 1 回適用 📋 (make-or-break)
- [ ] Phase P7 — 普遍確率下界 (CT 14.6.1) 📋
- [ ] Phase P8 — Levin 符号化定理 (等号、**flagship** `@[entry_point]`、crux) 📋
- [ ] Phase P9 — Chaitin Ω (§14.9) 📋
- [ ] Phase P10 — Kolmogorov 十分統計量 (§14.12、stretch、最重量) 📋

**第 2 波の control state (cold-read 用)**: gateway atom が唯一の make-or-break。通れば P7 下界と P9 Ω 収束は
Kraft + summable + `le_tsum` で直線化。P8 等号方向 (Levin) が第 2 波唯一の真の crux (Shannon-Fano-Elias 逆向き構成)。
P10 は解析壁でなく最重量の定義量 (250–500 行) = 撤退候補で DAG 末尾の stretch。**第 2 波に genuine な Mathlib
解析壁は無い** (Kraft 既存、下記 settled facts) ⟹ 途中 sorry は全て object 別 `plan:` slug、`wall:` を打つ先は
現状無い (gateway-atom-first で実測して初めて壁判定)。

## ゴール / Scope

**最終到達点 (flagship)**: Levin 符号化定理 (CT 2nd ed §14.6、番号は着手前に PDF 照合)
`|-log₂ P_U(x) - K(x)| ≤ c` — 普遍確率 P_U と prefix 複雑性 K が O(1) で一致する等式。これを
`@[entry_point]` headline `levin_coding_theorem` に据え、prefix 塔の頂点とする。

**In (第 2 波)**: gateway atom (prefix-free 機械 U_pf + K + P_U + Kraft 1 回適用) → **P7 普遍確率下界** (CT 14.6.1)
→ **P8 Levin 符号化定理** (等号、flagship) → **P9 Chaitin Ω** (§14.9、収束 + 非計算性) → **P10 Kolmogorov
十分統計量** (§14.12、stretch)。P10 はユーザー確定で本 moonshot の最終 Phase に含めるが、honest に「最重量の
定義量ビルド (250–500 行)、撤退ライン候補」と扱い DAG 上は P7–P9 closure 後の stretch 位置に置く。

**Out (非ゴール)**: Mathlib への PR / upstream、prefix 複雑性 K の bit↔nat 精密変換の作り込み、
Martin-Löf randomness の一般理論 (P9 の「algorithmically random」主張に要る範囲を超えた展開)。

---

## Approach

### 第 2 波全体の DAG

```
        Phase M0  Mathlib API 在庫調査 ✅ (w2-inventory.md が SoT、Kraft 既存の overturn 確定)
                 │
                 ▼
   ╔══ Gateway atom (make-or-break) ══╗
   ║  prefix-free 機械 U_pf 構成         ║  通れば残り直線化 / 詰まれば定義形再設計 (R-W2a)
   ║  + K 定義 + P_U 定義 + Kraft 1 回適用 ║
   ╚══════════════╤═══════════════════╝
                  ▼
   ┌──── P7 普遍確率下界 ────┐  P_U(x) ≥ 2^{-K(x)}  (ENNReal.le_tsum 1 項下界、○ 軽い)
   │                        │
   ▼                        ▼
P9 Chaitin Ω             P8 Levin 符号化定理 (等号、flagship、crux △)
 収束 (Kraft+summable ○)     K(x) ≤ -log₂ P_U(x) + c  (Shannon-Fano-Elias 逆向き構成、self-build の山)
 + 非計算性 (halting 転用)     └── P7 (≤) と合流 ⟹ |K + log₂ P_U| ≤ c
   │                        │
   └────────┬───────────────┘
            ▼
        P10 Kolmogorov 十分統計量 (§14.12、stretch、最重量定義量 250–500 行、撤退候補)
```

### gateway atom = 第 2 波の礎石 (3–4 点セット、第 1 波 gateway の型を踏襲)

第 1 波の gateway atom (U 構成 + P1 + P2 literal) が背骨全体の make-or-break だったのと同型に、第 2 波は
**prefix-free 機械 U_pf の構成を礎石**とする。1 本で以下 3–4 点を通す:

1. **`PrefixFree (S : Set (List Bool)) : Prop`** 述語 (`List.IsPrefix` から数行) + **prefix ⟹ UniquelyDecodable**
   の橋 (Mathlib 不在、self-build 数行) + **UD の下方単調性** (有限部分集合への適用に要る、~5 行)。
2. **`prefixUniversalEval : List Bool → Part ℕ`** — 自己限定 (self-delimiting) 2 モード parse 機械。
   literal モードの payload 長を自己限定符号 (Elias γ / 長さ前置) で前置し、valid-program 集合が prefix-free に
   なる構成。**これが第 2 波最大の自作の山 (150–300 行)**。interpret モードは第 1 波と同じく Mathlib `eval` 委譲。
3. **`prefixComplexity` (K) / `universalProb` (P_U : ℝ≥0∞) の定義** (Mathlib-shape-driven、下記)。
4. **Kraft 1 回適用**: valid-program 集合の各有限部分集合に `PrefixFree.uniquelyDecodable` +
   `kraft_mcmillan_inequality` (α = Bool、base 1/2) を適用 ⟹ `∀ u, ∑_{p∈u} 2^{-|p|} ≤ 1` を出し、P7 / P9 の
   `≤ 1` / summable の下地を確定させる。

**make-or-break の判定**: (2) の自己限定 literal 符号が組めて (4) の Kraft 接続が通れば、P7 下界と P9 Ω 収束は
`ENNReal.le_tsum` / `summable_of_sum_le` で直線的に閉じる。**詰まれば定義形を再設計 (R-W2a)** — 第 1 波
`universalEval` の literal `false::bs` は前置閉なので**そのまま使えず** U_pf は別構成 (inventory §E ⚠️)。

### under-estimation ガード (壁/非壁を額面で受けない)

inventory は全 P を downgrade した (P7 △→○、P8 ✖→△、P9 ✖→○〜△) が、本計画は
**gateway-atom-first で実測するまで壁/非壁を確定しない** (CLAUDE.md「not-a-wall を額面で受けない」)。特に
**P8 等号方向は crux として保守的に**扱う — Kraft は「符号が存在する必要条件」しか与えず、P_U の質量に見合う
prefix program を実際に構成する部分 (Kraft の逆向き) は self-build。inventory の「○/△」は着手前の見積であり、
gateway atom が実装で通って初めて壁見立ての確度が上がる。

### 定義形 (Mathlib-shape-driven、consumed lemma の conclusion form に合わせる)

消費する Mathlib lemma の結論形に定義を合わせる (CLAUDE.md「Mathlib-shape-driven Definitions」):

- **K = `prefixComplexity x := sInf { l | ∃ p : List Bool, p.length = l ∧ x ∈ prefixUniversalEval p }`** —
  第 1 波 `condComplexity` の `sInf` 到達性型を踏襲。非空性は「記述可能な x」に限る (P_U(x)>0 ⟺ K(x) 有限)。
- **P_U = `universalProb x := ∑' p : {p // x ∈ prefixUniversalEval p}, (2:ℝ≥0∞)⁻¹ ^ p.length` (ℝ≥0∞ 値)** —
  `ENNReal.tsum_eq_iSup_sum` で **tsum が常時定義 ⟹ 収束証明が消える**。下界は `ENNReal.le_tsum` の 1 項、
  `≤ 1` は `ENNReal.sum_le_tsum` + Kraft(有限)。`-log` は `ENNReal.log : ℝ≥0∞ → EReal` と型が噛む。
- **Ω = `chaitinOmega := ∑' p : {p // (prefixUniversalEval p).Dom}, (2:ℝ≥0∞)⁻¹ ^ p.length` (ℝ≥0∞ 値)** — 同上。
- **設計判断 (inventory 採用)**: 第 1 波 `universalEval` を prefix-free 版に**拡張はしない** — literal `false::bs`
  が前置閉ゆえ U_pf は**別機械を建てる**。再利用するのは interpret モードの `eval (ofNat Code idx)` 委譲機構のみ
  (手組み回避)。P8 最終不等式 `|K + log₂ P_U| ≤ c` は ℝ の絶対値なので `EReal → ℝ` の `.toReal` 変換
  (P_U(x) ∈ (0,1] で有限) が要る (plumbing、P_U(x)>0 の担保が前提)。

### 第 1 波からの read-only 消費資産 (署名変更しない ⟹ consumer ripple 解析不要)

すべて `InformationTheory/Shannon/Kolmogorov/` に proof-done で既存。第 2 波は署名を触らず消費する:

| 資産 | file:line | 第 2 波での役割 |
|---|---|---|
| `complexity x` / `condComplexity x y` | `UniversalMachine.lean:102/106` | K ≥ C の比較対象 + K 設計の雛形 |
| interpret 委譲機構 (`eval (ofNat Code idx)`) | `UniversalMachine.lean:54` 内 | U_pf の interpret モードに流用 (手組み回避) |
| `invariance` / `invariance_code` | `Invariance.lean:53/36` | prefix 不変性の pointwise-over-descriptions 雛形 |
| `incompressible_count` | `Counting.lean:108` | K 版数え上げの雛形 (Kraft でより精密化可) |
| `complexity_not_computable` / `condComplexity_not_computable` | `Noncomputable.lean:83/40` | **P9 Ω 非計算性の Berry 論法 転用先** |
| `entropy μ Xs` | `Bridge.lean:40` | P10 KSS / MDL の H(X) 項 |
| `ComputablePred.halting_problem` | `Mathlib/Computability/Halting.lean:65` | P9 Ω 非計算性の背骨 (第 1 波 P5 と同弾) |

### 実装原則

- **Skeleton-driven**: 各 Phase は全補題を `:= by sorry` で建て type-check done を確認してから 1 sorry ずつ充填。
  inventory §着手 skeleton (`PrefixMachine.lean` 出だし) がそのまま Gateway atom の skeleton。
- **並走レーン**: P9 収束 (Kraft plumbing) と P7 下界は gateway atom が通れば互いに独立。P9 非計算性は第 1 波
  halting 資産のみ依存で P8 と並走可 (撤退ライン R-W2b の最小成果でもある)。
- **signature 変更なし**: 第 2 波は第 1 波資産を read-only 消費する新規定義群であり、既存 shared lemma の
  signature 変更は無い ⟹ `dep_consumers` による consumer ripple 解析は不要。

---

## Phase 詳細

各 Phase: 依存 / 成果物 (signature 略式) / 見積行数 / proof-log / 撤退ライン。

### Phase M0 — Mathlib API 在庫調査 ✅

- **状態**: DONE。[`kolmogorov-w2-inventory.md`](kolmogorov-w2-inventory.md) (340 行) が SoT。Kraft-McMillan
  (有限 UD 符号版) + `summable_of_sum_le` + `ENNReal.tsum_eq_iSup_sum` が Ω/P_U 収束を供給する overturn を
  machine/loogle 確認済み。§Key-preconditions box (Kraft の有限性・型クラス・ℝ≥0∞ 設計) が着手前の必読。
- **proof-log**: no (調査 Phase)。

### Gateway atom — prefix-free 機械 U_pf + K + P_U + Kraft 1 回適用 (make-or-break) 📋

- **依存**: 第 1 波 `UniversalMachine.lean` (interpret 委譲機構、read-only)。**make-or-break** — 通れば P7/P9 は
  直線化、詰まれば定義形を再設計 (R-W2a)。
- **成果物**: `PrefixFree` 述語 + `PrefixFree.uniquelyDecodable` (Kraft 接続の橋) + UD 下方単調性 +
  `prefixUniversalEval : List Bool → Part ℕ` (自己限定 2 モード parse) + `prefixComplexity` (K) +
  `universalProb` (P_U : ℝ≥0∞) + valid-program 集合への Kraft 1 回適用 (`∀ u, ∑ 2^{-|p|} ≤ 1`)。
- **見積行数**: **150–300 行** (自己限定 literal 符号 = 第 2 波最大の新規分、interpret は第 1 波流用で軽い)。
  ファイル `PrefixMachine.lean`。
- **proof-log**: **yes** (gateway atom を含む foundation、metrics をデモ資産として取得)。
- **撤退ライン**: 自己限定 literal 符号が 1 セッションで組めない → **R-W2a 発動** (interpret-only 機械へ退避、
  K の domain を「停止 program の像」に絞り P9 Ω を最小成果に先取り)。退避出口は
  `sorry + @residual(plan:kolmogorov-w2-prefix-machine)`。`IsPrefixMachineHypothesis` 等に self-delimiting 性を
  畳んで P8 を「通ったことにする」load-bearing bundling は**禁止** (CLAUDE.md 検証の誠実性)。

### Phase P7 — 普遍確率下界 (CT 14.6.1) 📋

- **依存**: Gateway atom (P_U 定義 + Kraft)。
- **成果物**: `universalProb_ge_two_pow_neg_prefixComplexity (x) : (2:ℝ≥0∞)⁻¹ ^ prefixComplexity x ≤
  universalProb x` (P_U(x) ≥ 2^{-K(x)})。系: `-log₂ P_U(x) ≤ K(x)` (P8 の ≤ 方向)。
- **見積行数**: **60–120 行** (定義 + well-defined + 下界)。最短 program p* (長さ K(x)) の寄与を
  `ENNReal.le_tsum` の 1 項下界で取るだけ ⟹ **○ 軽い** (inventory 実測、scouting △ → ○ 格上げ)。ファイル
  `UniversalProbability.lean`。
- **proof-log**: no。
- **撤退ライン**: 発動見込み低 (Kraft + le_tsum で片側は軽い)。単独退避は
  `sorry + @residual(plan:kolmogorov-w2-universal-prob)`。

### Phase P8 — Levin 符号化定理 (等号、flagship `@[entry_point]`、crux) 📋

- **依存**: P7 (≤ 方向) + Gateway atom (P_U, K)。**第 2 波唯一の真の crux**。
- **成果物** (`@[entry_point]`、CT §14.6):
  ```lean
  theorem levin_coding_theorem :
      ∃ c : ℕ, ∀ x : ℕ, 0 < universalProb x →
        |(-(Real.logb 2 (universalProb x).toReal)) - (prefixComplexity x : ℝ)| ≤ c
  ```
  (境界 `0 < P_U x` = 記述可能な x に限定。P_U(x)=0 で `ENNReal.log 0 = ⊥`、落とすと不等式が破れる ―
  inventory Key-preconditions box、verbatim 確認済 `log_zero = ⊥`)。
- **証明戦略**: (≤) = P7 の 1 項下界 (軽い)。(≥) = **K(x) ≤ -log₂ P_U(x) + c** — P_U(x) の質量から長さ
  `≈ -log₂ P_U(x)` の prefix program を Shannon-Fano-Elias (算術符号) で**逆向きに構成**。Kraft は符号の存在の
  必要条件を与えるが、実際の構成は Kraft の逆向きで self-build。両側を合流し `|K + log₂ P_U| ≤ c`。
- **見積行数**: **200–400 行** (第 2 波最大の山、逆向き構成)。ファイル `Levin.lean`。
- **proof-log**: **yes** (crux、method のデモ資産)。
- **撤退ライン**: 等号 crux が 400 行超で発散 → **R-W2b 発動** (P7 下界 + P9 Ω の 2 headline を第 2 波の最小
  成果に確定、P8 は park)。退避出口 `sorry + @residual(plan:kolmogorov-w2-levin)`。R-W2b 発動公算 = **中**。

### Phase P9 — Chaitin Ω (§14.9) 📋

- **依存**: Gateway atom (Kraft + summable、収束) + 第 1 波 `complexity_not_computable` / `halting_problem`
  (非計算性)。P8 と独立に走れる = **並走レーン**。
- **成果物**: `chaitinOmega : ℝ≥0∞` の定義 + `chaitinOmega_le_one : chaitinOmega ≤ 1` (収束) +
  `¬ Computable`-系の非計算性 (Ω の各 bit が停止問題を解く古典論法)。余力で「algorithmically random」の主張
  (Out 節の範囲内に留める)。
- **見積行数**: **80–150 行** (収束は Kraft で軽い plumbing、非計算性が本体)。ファイル `Omega.lean`。
- **proof-log**: no。
- **撤退ライン**: 収束は壁でなく plumbing (発動見込み低)。非計算性が発散したら収束部分 (`≤ 1`) のみ先に確定。
  単独退避は `sorry + @residual(plan:kolmogorov-w2-omega)`。

### Phase P10 — Kolmogorov 十分統計量 (§14.12、stretch、最重量) 📋

- **依存**: prefix K (Gateway atom) + 第 1 波 `entropy` (`Bridge.lean:40`)。DAG 末尾の stretch。
- **成果物**: モデル `S ∋ x` の記述長 `K(S) + log|S|`、最小十分統計量、MDL 原理の定式化。
- **見積行数**: **250–500 行** (第 2 波最重量、解析壁ではなく**定義量が多い**)。ファイル `SufficientStatistic.lean`。
- **proof-log**: **yes** (定義量が多く設計判断を残す価値)。
- **撤退ライン**: **本 Phase 全体が撤退候補**。P7–P9 closure が第 2 波の成立条件であり、P10 が 1 セッションで
  定義群を組めない場合は第 2.5 波へ park (P7–P9 の成否には無関係)。park slug `plan:kolmogorov-w2-kss`。

---

## 撤退ライン (frozen slug)

第 2 波固有の撤退ライン。frozen slug は他文書参照ありうるため確定後も register に残す。

- **R-W2a** (gateway atom、prefix literal 自己限定符号が組めない → 定義形再設計): U_pf の literal モード
  自己限定符号 (Elias γ / 長さ前置) が 1 セッションで組めない場合 → **縮退**: U_pf を「literal を持たない
  interpret-only 機械」に退避し、K の well-defined 性は「記述可能な x に限定」(P7/P9 の domain を「停止 program
  の像」に絞る) で先に P9 Ω (収束 + 非計算) を最小成果に確定。退避出口 =
  `sorry + @residual(plan:kolmogorov-w2-prefix-machine)`。**hypothesis bundling 禁止** (`IsPrefixMachineHypothesis`
  に self-delimiting 性を畳んで P8 を通したことにするのは load-bearing = 禁止)。発動公算 = 中。
- **R-W2b** (P8 等号 crux が 400 行超で発散 → P7+P9 最小成果先取り): P7 普遍確率下界 + P9 Ω (収束 + 非計算性) の
  2 headline を第 2 波の最小成果として先に確定 (両者は Kraft + summable + le_tsum で軽い)、P8 Levin は第 2.5 波へ
  park。退避出口 = `sorry + @residual(plan:kolmogorov-w2-levin)`。**発動公算 = 中** (P8 等号方向が第 2 波唯一の
  重量級)。

**判定 (現時点)**: 撤退ライン未発動 (第 2 波未着手)。R-W2a は自己限定符号が組めれば回避可、R-W2b は crux の
行数次第。

---

## residual slug 方針

inventory 推奨に従い **第 1 波 §Out の単一 `wall:prefix-free-tower` は撤回** (over-estimation、Kraft 既存)。
第 2 波の途中 sorry は **object 別の `plan:` slug** に分割し、各 slug は将来分割する子 plan の filename stem
(kebab-case、`-plan.md` を除く) と一致させる:

| slug (`@residual(plan:…)`) | 対応子 plan (未作成、分割時に起票) | object |
|---|---|---|
| `kolmogorov-w2-prefix-machine` | `kolmogorov-w2-prefix-machine-plan.md` | Gateway atom (U_pf / PrefixFree / K) |
| `kolmogorov-w2-universal-prob` | `kolmogorov-w2-universal-prob-plan.md` | P7 P_U 定義 + 下界 |
| `kolmogorov-w2-omega` | `kolmogorov-w2-omega-plan.md` | P9 Ω 収束 + 非計算性 |
| `kolmogorov-w2-levin` | `kolmogorov-w2-levin-plan.md` | P8 等号 crux |
| `kolmogorov-w2-kss` | `kolmogorov-w2-kss-plan.md` | P10 十分統計量 |

**`wall:` を打つ先は現状無い** — P8 crux も「Shannon-Fano-Elias 構成という self-build」= 選択 (big) であって
Mathlib 不在の解析 (hard) ではない。gateway atom を実装で実測して初めて genuine 壁判定ができる (それまでは
plan slug)。genuine `wall:` が実測で現れたらその時点で `docs/audit/audit-tags.md` の Wall register に追記する。

---

## settled facts (machine/loogle 確認済み、facts 台帳が無いため本節に保持)

`docs/kolmogorov/kolmogorov-facts.md` は未作成。以下は confidence = `machine` / `loogle-neg`。expensive-to-
re-derive (Mathlib 実ファイル Read + loogle) につきここに保持する:

- **claim (overturn、confidence = `machine`)**: scouting §0/§3「prefix-free 機械 / program 上の Kraft = 完全に
  不在、本章唯一の genuine 解析壁」は **Kraft の解析核については誤り** (over-estimation)。実在資産:
  - `InformationTheory.UniquelyDecodable (S : Set (List α)) : Prop`
    @ `Mathlib/InformationTheory/Coding/UniquelyDecodable.lean` (L35)
  - `InformationTheory.kraft_mcmillan_inequality {S : Finset (List α)} [Fintype α] [Nonempty α]
    (h : UniquelyDecodable (↑S)) : ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1`
    @ `Mathlib/InformationTheory/Coding/KraftMcMillan.lean` (L149)
  - 無限化の橋: `summable_of_sum_le` @ `Mathlib/Topology/Algebra/InfiniteSum/Real.lean:84` +
    `ENNReal.tsum_eq_iSup_sum` @ `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean:71`
- **再検証コマンド**: `Read Mathlib/InformationTheory/Coding/KraftMcMillan.lean` (L149) +
  `Mathlib/InformationTheory/Coding/UniquelyDecodable.lean` (L35)。loogle `"Kraft"` → Found 1、
  `"PrefixFree"` / `"MartinLof"` / `"Chaitin"` → Found 0 (いずれも定義の自作 = 選択、壁でない)。
- **含意**: 第 2 波は「壁」でなく「新規定義群 (解析は Kraft で調達済)」。`@residual(wall:prefix-free-tower)` 単一壁
  slug は撤回、object 別 `plan:` slug に分割 (上記表)。

**Key-preconditions (着手前の事故ポイント、SoT は inventory §Key-preconditions box)**:

- `kraft_mcmillan_inequality` は `S : Finset` = **有限符号**が必須。Ω / P_U の domain (停止 prefix program 全体) は
  **可算無限** ⟹ Kraft を各有限部分集合に適用 → `summable_of_sum_le` (c=1) / `ENNReal.sum_le_tsum` で無限化する
  (唯一の型整合ルート、「Kraft を無限集合に直接適用」は型が合わず不可)。
- Kraft の hypothesis は `UniquelyDecodable` (prefix-free ではない) ⟹ **prefix-free ⟹ UD の橋** (自作数行、
  `List.IsPrefix` から) + **UD 下方単調性** (`S'⊆S ∧ UD S ⟹ UD S'`、自作 ~5 行) を Gateway atom で用意。
- `[Fintype α] [Nonempty α]` は `α = Bool` で自動充足 (base = 1/2)。program を `List Bool` で建てること
  (第 1 波判断ログ #2(ii) を踏襲、ℕ-as-binary だと α が定まらず Kraft が使えない)。

---

## ファイル構成 / 分割方針

新ファイルは第 1 波と同じ `InformationTheory/Shannon/Kolmogorov/` 配下。各 1500 行未満:

- `PrefixMachine.lean` — Gateway atom (`PrefixFree` / `PrefixFree.uniquelyDecodable` / UD 単調性 /
  `prefixUniversalEval` / `prefixComplexity` / Kraft 1 回適用)
- `UniversalProbability.lean` — P7 (`universalProb` 定義 + 下界)
- `Omega.lean` — P9 (`chaitinOmega` 定義 + `≤ 1` + 非計算性)
- `Levin.lean` — P8 (等号 crux、flagship)
- `SufficientStatistic.lean` — P10 (KSS / MDL、stretch)

各ファイル追加時に `InformationTheory.lean` へ import 行を登録。`private` helper を共有する sub-module は
同一ファイルに置く (file-scoped `private`)。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正時。決着済 entry は削除 (git が履歴)、active な判断のみ残す。

1. **単一壁 slug の撤回 (active、settled facts と対)**: 第 1 波 §Out / 判断ログ #1 の
   `@residual(wall:prefix-free-tower)` は over-estimation (Kraft 既存)。第 2 波の途中 sorry は object 別 `plan:`
   slug に分割し、genuine `wall:` を打つ先は gateway-atom-first で実測するまで確定しない。
2. **U_pf は第 1 波 `universalEval` の拡張でなく別機械 (active、inventory 採用)**: literal `false::bs` が前置閉で
   prefix-free でないため。再利用は interpret 委譲機構のみ。§定義形の設計判断。
3. **P8 等号方向を crux として保守的に (active、under-estimation ガード)**: inventory の P8 ✖→△ は着手前見積。
   Kraft は符号存在の必要条件しか与えず、P_U 質量からの prefix program 構成 (Kraft 逆向き) は self-build。
   実測で壁見立ての確度を上げる。R-W2b 発動公算 = 中。

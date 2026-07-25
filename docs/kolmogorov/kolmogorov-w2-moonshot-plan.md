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
- [x] Gateway atom — prefix-free 機械 U_pf + K + P_U + Kraft 1 回適用 ✅ (`PrefixMachine.lean`、`537c5ab8`/`a448b313`)
- [x] Phase P7 — 普遍確率下界 (CT 14.6.1) ✅ (`UniversalProbability.lean`、`16ce3108`/`4303c4b6`)
- [ ] Phase P8 — Levin 符号化定理 (等号、**flagship** `@[entry_point]`、crux) 📋 ← **次のマイルストーン**
- [ ] Phase P9 — Chaitin Ω (§14.9) 🚧 Ω 収束 + prefix K 非計算性は着地 (`Omega.lean`、`4f55f459`/`07057aa1`)、
      **Ω 自体の非計算性のみ未了** → park (`plan:kolmogorov-w2-omega-noncomputable`)
- [ ] Phase P10 — Kolmogorov 十分統計量 (§14.12、stretch、最重量) 📋

**第 2 波の control state (cold-read 用)**: gateway atom は通過 ⟹ make-or-break は解消し **R-W2a は回避**
(自己限定符号が実際に組めた)。P7 は DONE、P9 は Ω 収束 (`chaitinOmega_le_one`) + **prefix K の非計算性**
(`prefixComplexity_not_computable`) まで着地し、**Ω 自体の非計算性だけが未了** (park、下記 slug 表)。
**次のマイルストーンは P8 = 第 2 波唯一の真の crux** (Shannon-Fano-Elias 逆向き構成、撤退ライン R-W2b が active、
着手前に §Phase P8 の strength diff を必ず 1 回通すこと)。P10 は解析壁でなく最重量の定義量 (250–500 行) =
撤退候補で DAG 末尾の stretch のまま。`wall:` を打つ先は現状無い (genuine 壁判定は実測後に初めて行う)。
途中 sorry の残置状況は plan に焼き込まず `rg "@residual" InformationTheory/Shannon/Kolmogorov/` で都度確認する。

## ゴール / Scope

**最終到達点 (flagship)**: Levin 符号化定理 (CT 2nd ed §14.6、番号は着手前に PDF 照合)
`|-log₂ P_U(x) - K(x)| ≤ c` — 普遍確率 P_U と prefix 複雑性 K が O(1) で一致する等式。これを
`@[entry_point]` headline `levin_coding_theorem` に据え、prefix 塔の頂点とする。

**In (第 2 波)**: gateway atom (prefix-free 機械 U_pf + K + P_U + Kraft 1 回適用) → **P7 普遍確率下界** (CT 14.6.1)
→ **P8 Levin 符号化定理** (等号、flagship) → **P9 Chaitin Ω** (§14.9、収束 + 非計算性。**Ω 自体の非計算性は
park**、§Phase P9) → **P10 Kolmogorov 十分統計量** (§14.12、stretch)。P10 はユーザー確定で本 moonshot の最終 Phase に含めるが、honest に「最重量の
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
   ╔══ Gateway atom ✅ (通過、R-W2a 回避) ══╗
   ║  prefix-free 機械 U_pf 構成            ║  自己限定 (単進長さ前置) literal 符号が実際に組めた
   ║  + K 定義 + P_U 定義 + Kraft 1 回適用   ║  ⟹ 残り直線化
   ╚══════════════╤════════════════════════╝
                  ▼
   ┌──── P7 普遍確率下界 ✅ ────┐  P_U(x) ≥ 2^{-K(x)} + 対数形 (Levin の ≤ 方向は取得済)
   │                          │
   ▼                          ▼
P9 Chaitin Ω 🚧              P8 Levin 符号化定理 (等号、flagship、crux △) ← 次のマイルストーン
 収束 ✅ (chaitinOmega_le_one)   K(x) ≤ -log₂ P_U(x) + c  (Shannon-Fano-Elias 逆向き構成、self-build の山)
 prefix K 非計算性 ✅            ⚠️ 着手前に prefix invariance の strength diff (2 倍係数) を 1 回通す
 Ω 自体の非計算性 → park        └── P7 (≤) と合流 ⟹ |K + log₂ P_U| ≤ c
   │                          │
   └────────┬─────────────────┘
            ▼
        P10 Kolmogorov 十分統計量 (§14.12、stretch、最重量定義量 250–500 行、撤退候補)
```

### gateway atom = 第 2 波の礎石 ✅ (下流が消費する API)

第 1 波と同型に **prefix-free 機械 U_pf の構成を礎石**とした make-or-break は通過済み。以降の Phase が
read-only 消費する API (`PrefixMachine.lean`、署名は都度 `scripts/sig_view.ts` で確認):

- `PrefixFree` 述語 / `PrefixFree.mono` / `PrefixFree.uniquelyDecodable` / `uniquelyDecodable_mono` (Kraft 接続の橋)
- `selfDelimit` (**単進長さ前置**ラッパ、`bs.length` 個の `true` + `false` + payload) / `parseUnary_selfDelimit` /
  `range_selfDelimit_prefixFree` — **U_pf の受理 program は必ず `selfDelimit payload` の形** ⟹ `|p| = 2·|payload| + 1`
  (この 2 倍が P8 の strength diff の源、§Phase P8 の ⚠️)
- `prefixUniversalEval` (自己限定 2 モード parse) / `prefixLiteralProg` + `prefixUniversalEval_literal` (literal 入口) /
  `prefixUniversalEval_dom_prefixFree` / `prefixUniversalEval_kraft` (有限 Kraft)
- **`tsum_inv_two_pow_length_le_one`** — P9 leg で追加された汎用 plumbing (有限 Kraft → 可算無限 lift)。
  P_U / Ω 双方の `≤ 1` がこれで 2–3 行になる:
  ```lean
  theorem tsum_inv_two_pow_length_le_one {P : List Bool → Prop}
      (hP : ∀ p, P p → (prefixUniversalEval p).Dom) :
      ∑' p : { p : List Bool // P p }, (2 : ℝ≥0∞)⁻¹ ^ (p : List Bool).length ≤ 1
  ```
- `prefixComplexity` (K、`sInf`) / `prefixComplexity_set_nonempty` / `prefixComplexity_spec` (最短 program の到達性、
  **literal 入口ゆえ全 `x : ℕ` で非空 = K は total**) / `universalProb` (P_U : ℝ≥0∞)

### under-estimation ガード (壁/非壁を額面で受けない)

inventory は全 P を downgrade した (P7 △→○、P8 ✖→△、P9 ✖→○〜△) が、本計画は
**gateway-atom-first で実測するまで壁/非壁を確定しない** (CLAUDE.md「not-a-wall を額面で受けない」)。gateway atom /
P7 / P9 の実測でこの見立ては当たったが、**P8 等号方向は依然 crux として保守的に**扱う — Kraft は「符号が存在する
必要条件」しか与えず、P_U の質量に見合う prefix program を実際に構成する部分 (Kraft の逆向き) は self-build。
さらに P9 で判明した prefix invariance の **2 倍係数** (weaker relative) が P8 の等号に直接効く (§Phase P8 ⚠️) ため、
P7/P9 が軽かったことを P8 の軽さの証拠として読まないこと。

### 定義形 (Mathlib-shape-driven、consumed lemma の conclusion form に合わせる)

消費する Mathlib lemma の結論形に定義を合わせる (CLAUDE.md「Mathlib-shape-driven Definitions」):

- **K = `prefixComplexity x := sInf { l | ∃ p : List Bool, p.length = l ∧ x ∈ prefixUniversalEval p }`** —
  第 1 波 `condComplexity` の `sInf` 到達性型を踏襲。**着地形では domain 制限は不要**: literal 入口
  (`prefixLiteralProg` + `prefixUniversalEval_literal`) が全 `x : ℕ` の記述を与えるので
  `prefixComplexity_set_nonempty` は無条件 ⟹ K は total、`prefixComplexity_spec` で最短 program が到達する。
- **P_U = `universalProb x := ∑' p : {p // x ∈ prefixUniversalEval p}, (2:ℝ≥0∞)⁻¹ ^ p.length` (ℝ≥0∞ 値)** —
  `ENNReal.tsum_eq_iSup_sum` で **tsum が常時定義 ⟹ 収束証明が消える**。下界は `ENNReal.le_tsum` の 1 項、
  `≤ 1` は `tsum_inv_two_pow_length_le_one`。
- **Ω = `chaitinOmega := ∑' p : {p // (prefixUniversalEval p).Dom}, (2:ℝ≥0∞)⁻¹ ^ p.length` (ℝ≥0∞ 値)** — 同上。
- **対数形の型 (着地した規約、P8 はこれを踏襲)**: 当初 `ENNReal.log : ℝ≥0∞ → EReal` との型噛みを警戒していたが、
  P7 は **`.toReal` を先に取って `Real.logb 2` を使う**形で閉じた (`neg_logb_universalProb_le_prefixComplexity`)。
  `P_U(x) ≠ ⊤` は `universalProb_le_one` から、`0 < P_U(x)` は下界 + `ENNReal.pow_pos` から出るので、
  **`0 < universalProb x` を仮説に置く必要はない** (P8 flagship の署名に影響 → §Phase P8)。
- **設計判断 (inventory 採用)**: 第 1 波 `universalEval` を prefix-free 版に**拡張はしない** — literal `false::bs`
  が前置閉ゆえ U_pf は**別機械を建てる**。再利用するのは interpret モードの `eval (ofNat Code idx)` 委譲機構のみ
  (手組み回避)。

### 第 1 波からの read-only 消費資産 (署名変更しない ⟹ consumer ripple 解析不要)

すべて `InformationTheory/Shannon/Kolmogorov/` に proof-done で既存。第 2 波は署名を触らず消費する:

| 資産 | file:line | 第 2 波での役割 |
|---|---|---|
| `complexity x` / `condComplexity x y` | `UniversalMachine.lean:102/106` | K ≥ C の比較対象 + K 設計の雛形 |
| interpret 委譲機構 (`eval (ofNat Code idx)`) | `UniversalMachine.lean:54` 内 | U_pf の interpret モードに流用 (手組み回避) |
| `invariance` / `invariance_code` | `Invariance.lean:53/36` | prefix 不変性の pointwise-over-descriptions 雛形 |
| `incompressible_count` | `Counting.lean:108` | K 版数え上げの雛形 (Kraft でより精密化可) |
| `complexity_not_computable` / `condComplexity_not_computable` | `Noncomputable.lean:83/40` | **P9 prefix K 非計算性の Berry 論法 転用元** (転用済) |
| `entropy μ Xs` | `Bridge.lean:40` | P10 KSS / MDL の H(X) 項 |
| `ComputablePred.halting_problem` | `Mathlib/Computability/Halting.lean:65` | Ω 自体の非計算性 (park slug) の背骨候補 (第 1 波 P5 と同弾) |

### 実装原則

- **Skeleton-driven**: 各 Phase は全補題を `:= by sorry` で建て type-check done を確認してから 1 sorry ずつ充填。
  inventory §着手 skeleton (`PrefixMachine.lean` 出だし) がそのまま Gateway atom の skeleton。
- **並走レーン**: 残る並走可能レーンは P8 (crux) と Ω 自体の非計算性 (park slug、第 1 波 halting 資産のみ依存)。
- **第 1 波資産の signature 変更なし**: 第 2 波は第 1 波資産を read-only 消費する新規定義群 ⟹ 第 1 波側の
  consumer ripple 解析は不要。**ただし第 2 波内部の `prefixUniversalEval` を P8 で触る選択肢がある** —
  そのときの ripple は実測済 (§Phase P8 の consumer 表)。

---

## Phase 詳細

各 Phase: 依存 / 成果物 (signature 略式) / 見積行数 / proof-log / 撤退ライン。

### Phase M0 — Mathlib API 在庫調査 ✅

- **状態**: DONE。[`kolmogorov-w2-inventory.md`](kolmogorov-w2-inventory.md) (340 行) が SoT。Kraft-McMillan
  (有限 UD 符号版) + `summable_of_sum_le` + `ENNReal.tsum_eq_iSup_sum` が Ω/P_U 収束を供給する overturn を
  machine/loogle 確認済み。§Key-preconditions box (Kraft の有限性・型クラス・ℝ≥0∞ 設計) が着手前の必読。
- **proof-log**: no (調査 Phase)。

### Gateway atom — prefix-free 機械 U_pf + K + P_U + Kraft 1 回適用 ✅

- **状態**: DONE (`PrefixMachine.lean`、commits `537c5ab8` + honesty/style ゲート `a448b313`)。**R-W2a 回避** —
  自己限定 literal 符号 (単進長さ前置 `selfDelimit`) が実際に組め、Kraft 接続まで通った ⟹ make-or-break 解消。
  提供 API の一覧は §Approach「gateway atom = 第 2 波の礎石」。**P9 leg で `tsum_inv_two_pow_length_le_one`
  (有限 Kraft → 可算無限 lift の汎用 plumbing) が後から追加**され、P_U / Ω 双方の `≤ 1` を 2–3 行にした。
- **proof-log**: yes (取得済)。

### Phase P7 — 普遍確率下界 (CT 14.6.1) ✅

- **状態**: DONE (`UniversalProbability.lean`、commits `16ce3108` + ゲート `4303c4b6`)。実測 ~80 行 =
  見積 60–120 行の下側。
- **成果物** (3 本、いずれも仮説なし):
  ```lean
  @[entry_point] theorem universalProb_ge_two_pow_neg_prefixComplexity (x : ℕ) :
      (2 : ℝ≥0∞)⁻¹ ^ prefixComplexity x ≤ universalProb x
  theorem universalProb_le_one (x : ℕ) : universalProb x ≤ 1
  theorem neg_logb_universalProb_le_prefixComplexity (x : ℕ) :
      -Real.logb 2 (universalProb x).toReal ≤ (prefixComplexity x : ℝ)
  ```
- **P8 への含意**: 3 本目が **Levin の (≤) 方向そのもの**であり、しかも `0 < universalProb x` を仮説に持たない
  (K が total ⟹ P_U(x) ≥ 2^{-K(x)} > 0 が全 x で出る)。⟹ P8 は (≥) 方向だけを残す。
- **proof-log**: no。

### Phase P8 — Levin 符号化定理 (等号、flagship `@[entry_point]`、crux) 📋 ← 次のマイルストーン

- **依存**: P7 (≤ 方向、取得済) + Gateway atom (P_U, K) + P9 の interpret 入口。**第 2 波唯一の真の crux**。
- **成果物** (`@[entry_point]`、CT §14.6):
  ```lean
  theorem levin_coding_theorem :
      ∃ c : ℕ, ∀ x : ℕ,
        |(-(Real.logb 2 (universalProb x).toReal)) - (prefixComplexity x : ℝ)| ≤ c
  ```
  当初案の `0 < universalProb x →` ガードは**落としてよい** (P7 の下界 + `ENNReal.pow_pos` で全 x に対し
  `0 < P_U x`、§定義形「対数形の型」)。仮説を残すのは害はないが、無条件形が取れるなら無条件形を掲げる。
- **証明戦略**: (≤) = P7 の `neg_logb_universalProb_le_prefixComplexity` で**取得済**。(≥) = **K(x) ≤
  -log₂ P_U(x) + c** — P_U(x) の質量から長さ `≈ -log₂ P_U(x)` の prefix program を Shannon-Fano-Elias (算術符号) で
  **逆向きに構成**。Kraft は符号の存在の必要条件を与えるが、実際の構成は Kraft の逆向きで self-build。
- **着手コストを下げた新規資産 (P9 leg 由来)**: `prefixInterpretProg` / `prefixUniversalEval_interpret` /
  `prefix_invariance_code` により **U_pf の interpret モードの入口が開通**した (それまで in-tree の糊は
  `prefixUniversalEval_literal` = literal モードのみ)。⟹ P8 は「SFE 符号器を `Code` として与える」ところに集中できる。
  副次的に **Ω / P_U が literal 像だけの退化量でないこと**が機械的に裏書きされた (普遍性の非退化証人)。
- **⚠️ 着手前に必ず 1 回通す strength diff (textbook-object strength diff、CLAUDE.md)**:
  in-tree の prefix invariance は **`prefixComplexity x ≤ 2 * q.length + b`** (`Omega.lean:132/146` verbatim) で
  **線形係数 2**。教科書の prefix invariance は**加法的 `K(x) ≤ K_A(x) + c_A`** ⟹ 本実装は **weaker relative**。
  源は機械側: 受理 program は必ず `selfDelimit payload` (単進長さ前置、`PrefixMachine.lean:104`) で
  `|p| = 2·|payload| + 1`。Berry 論法 (P9) には十分だが、**この補題をそのまま再利用して Levin の等号を出すと
  加法定数に落ちない**。着手時の diff は 2 点:
  1. 2 倍は K 側と P_U 側の両方に効くので「等号が即偽」ではないが、**標準ルート (Kraft-Chaitin/SFE → invariance)
     が出すのは factor-2 版だけ** — 何が加法的に必要かを先に紙で確定する。
  2. 出口 3 択: (i) **SFE 記述を `q` そのものでなく自己限定済みの形で渡す設計**にして加法定数に落とす
     (実装者所見、機械の def は触らない = 第一候補) / (ii) U_pf に「符号自身の prefix-free 性が parse 境界を与える」
     モードを足す = **`prefixUniversalEval` の def 変更** (下の ripple を負う) / (iii) 着地した機械に対して真な形
     (factor-2 版) へ flagship を言い換え、**weaker relative であることを署名と docstring で明示**する。
     (iii) を選ぶ場合も「教科書 Levin を証明した」とは書かない (name laundering 禁止)。
- **(ii) を選ぶ場合の ripple (`scripts/dep_consumers.sh` 実測、root olean refresh 後)**:

  | target | direct consumers | 内訳 (file) |
  |---|---|---|
  | `prefixUniversalEval` | **21 decl / 3 file** | `PrefixMachine.lean` 10 / `Omega.lean` 9 / `UniversalProbability.lean` 2 |
  | `prefixComplexity` | **12 decl / 3 file** | `Omega.lean` 9 / `PrefixMachine.lean` 1 / `UniversalProbability.lean` 2 |
  | `universalProb` | **3 decl / 1 file** | `UniversalProbability.lean` 3 |

  import closure も同じ 3 ファイル (+ root) なので、機械の def 変更の影響は第 2 波内部に閉じる (第 1 波 / 他家系に
  波及しない)。ただし `prefixUniversalEval` を触ると `chaitinOmega` の値そのものが変わる = P9 の着地物 (収束 3 本 +
  非計算性) の**再証明が要る**点を見積に入れること。
- **見積行数**: **200–400 行** (第 2 波最大の山、逆向き構成)。ファイル `Levin.lean`。(ii) を選んだ場合は
  上表の ripple 分を上乗せ。
- **proof-log**: **yes** (crux、method のデモ資産)。
- **撤退ライン**: 等号 crux が 400 行超で発散 → **R-W2b 発動** (P7 下界 + P9 Ω の 2 headline を第 2 波の最小
  成果に確定、P8 は park)。退避出口 `sorry + @residual(plan:kolmogorov-w2-levin)`。R-W2b 発動公算 = **中**。

### Phase P9 — Chaitin Ω (§14.9) 🚧 部分 DONE

- **状態**: `Omega.lean` 着地 (commits `4f55f459` + ゲート `07057aa1`)。**入ったもの / 入っていないものを厳密に**:

  **入った (DONE)**:
  ```lean
  noncomputable def chaitinOmega : ℝ≥0∞
  @[entry_point] theorem chaitinOmega_le_one : chaitinOmega ≤ 1     -- 収束 (Kraft lift)
  theorem chaitinOmega_pos : 0 < chaitinOmega                       -- 退化 (Ω = 0) の排除
  theorem chaitinOmega_ne_top : chaitinOmega ≠ ⊤
  def prefixInterpretProg / theorem prefixUniversalEval_interpret   -- interpret モード入口
  theorem prefix_invariance_code / prefix_invariance                -- K(x) ≤ 2 * |q| + b (⚠️ P8 節)
  @[entry_point] theorem prefixComplexity_not_computable            -- prefix K の非計算性 (Berry)
  ```
  非計算性の補助 (`shortestPrefixProg` 系 / `exists_prefixIncompressible`) も同ファイルに同居。

  **入っていない (未了)**: **Ω 自体の非計算性** (「Ω の各 bit が停止問題を解く」古典論法)。当初この Phase の
  成果物欄はこれを含めていたが、着地したのは **K の非計算性であって Ω の非計算性ではない** — 両者は別 object。
  コード側 docstring は Ω の非計算性を一切主張していない (`Omega.lean` §Main results)。⟹ **park**:
  `plan:kolmogorov-w2-omega-noncomputable` (§residual slug 方針の表、着手時に子 plan を起票)。
  「algorithmically random」の主張も同 park に同梱 (Out 節の範囲を超えない範囲で)。
- **park の理由 (順序決定であって scope 落としではない)**: Ω 非計算性を述べるには「実数の計算可能性」の定式化を
  自前で建てる必要があり (Mathlib 不在、§settled facts の loogle 実測)、flagship の P8 を先に取る方が
  第 2 波全体の価値が高い。P8 / P10 の後に budget が残れば回収する。
- **proof-log**: no。

### Phase P10 — Kolmogorov 十分統計量 (§14.12、stretch、最重量) 📋

- **依存**: prefix K (Gateway atom) + 第 1 波 `entropy` (`Bridge.lean:40`)。DAG 末尾の stretch。
- **成果物**: モデル `S ∋ x` の記述長 `K(S) + log|S|`、最小十分統計量、MDL 原理の定式化。
- **見積行数**: **250–500 行** (第 2 波最重量、解析壁ではなく**定義量が多い**)。ファイル `SufficientStatistic.lean`。
- **proof-log**: **yes** (定義量が多く設計判断を残す価値)。
- **撤退ライン**: **本 Phase 全体が撤退候補**。第 2 波の成立条件は P7 / P8 / P9 (park 分を除く) の closure であり、
  P10 が 1 セッションで定義群を組めない場合は第 2.5 波へ park (P7–P9 の成否には無関係)。park slug
  `plan:kolmogorov-w2-kss`。

---

## 撤退ライン (frozen slug)

第 2 波固有の撤退ライン。frozen slug は他文書参照ありうるため確定後も register に残す。

- **R-W2a** (gateway atom、prefix literal 自己限定符号が組めない → 定義形再設計): **回避済 (未発動)** —
  自己限定符号 (単進長さ前置 `selfDelimit`) が実際に組め、Kraft 接続も通ったため縮退 (interpret-only 機械への
  退避 + K の domain 制限) は不要になった。slug は他文書参照のため register に残す。
- **R-W2b** (P8 等号 crux が 400 行超で発散 → 最小成果先取り): **active**。P7 普遍確率下界 + P9 Ω 収束 +
  prefix K 非計算性を第 2 波の最小成果として確定 (すでに着地済) し、P8 Levin は第 2.5 波へ park。退避出口 =
  `sorry + @residual(plan:kolmogorov-w2-levin)`。**発動公算 = 中** (P8 等号方向が第 2 波唯一の重量級。
  §Phase P8 の strength diff で「加法定数に落ちない」と判明した場合は、発散を待たず (iii) の言い換えか本ラインで
  park を選ぶ — factor-2 版を教科書 Levin と称するのは禁止)。

**判定 (現時点)**: R-W2a 回避済、R-W2b active (P8 未着手)。

---

## residual slug 方針

inventory 推奨に従い **第 1 波 §Out の単一 `wall:prefix-free-tower` は撤回** (over-estimation、Kraft 既存)。
第 2 波の途中 sorry は **object 別の `plan:` slug** に分割し、各 slug は将来分割する子 plan の filename stem
(kebab-case、`-plan.md` を除く) と一致させる:

| slug (`@residual(plan:…)`) | 対応子 plan (未作成、分割時に起票) | object |
|---|---|---|
| `kolmogorov-w2-prefix-machine` | `kolmogorov-w2-prefix-machine-plan.md` | Gateway atom (U_pf / PrefixFree / K) |
| `kolmogorov-w2-universal-prob` | `kolmogorov-w2-universal-prob-plan.md` | P7 P_U 定義 + 下界 |
| `kolmogorov-w2-omega` | `kolmogorov-w2-omega-plan.md` | P9 Ω 収束 (着地済、退避不要になった) |
| `kolmogorov-w2-omega-noncomputable` | `kolmogorov-w2-omega-noncomputable-plan.md` (未作成) | **Ω 自体の非計算性** (実数計算可能性の定式化 + U_pf の partrec 性) |
| `kolmogorov-w2-levin` | `kolmogorov-w2-levin-plan.md` | P8 等号 crux |
| `kolmogorov-w2-kss` | `kolmogorov-w2-kss-plan.md` | P10 十分統計量 |

`kolmogorov-w2-omega-noncomputable` は **`wall:` ではなく `plan:`** — 実数計算可能性が Mathlib に無いのは
「解析が難しい (hard)」ではなく「定式化と自作インフラを選ぶ (big)」側だからである (§settled facts の loogle 実測)。

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
  slug は撤回、object 別 `plan:` slug に分割 (上記表)。gateway atom / P7 / P9 が実装で通ったことでこの overturn は
  実測裏付け済 (第 1 波 §Out の撤回記録と対。`plan_lint` の
  `wall slug 'wall:prefix-free-tower' が code に無い` STALE は**この撤回記録そのものが源で benign**)。

- **claim (confidence = `loogle-neg`)**: **Mathlib に「計算可能実数 / 計算可能解析」の資産は無い**。
  - クエリ `Computable, Real` → **Found 0 declarations** / `ComputableReal` → **unknown identifier**
  - **含意**: 「Ω は計算不可能」を述べるには **「実数が計算可能」の定義を自前で建てる**必要がある。さらにその
    証明の最初の非自明ブロックは **`prefixUniversalEval` の partrec 性** (`List Bool ↔ ℕ` 符号化越しに
    `parseUnary` / `decodeNat` の computability を通す) で、これは現状 in-tree にも無い。
  - **候補定式化 3 つ** (後続 leg が再調査せず拾えるよう保持):
    (i) `IsComputableReal` 自前定義 (計算可能有理近似列 + 計算可能収束率) → `¬ IsComputableReal Ω`。
        古典的に正統だが重い。
    (ii) `¬ ComputablePred (fun n ↦ (prefixUniversalEval (decode n)).Dom)` (prefix 機械の停止問題の決定不能性)。
        実数計算可能性の定義を建てずに Ω 非計算性の中身を述べられる。`ComputablePred.halting_problem`
        (`Mathlib/Computability/Halting.lean:65`) からの帰着。**実装者の推奨**。
    (iii) 別 leg / 子 plan に切り出す (= 今回採用した順序、slug `plan:kolmogorov-w2-omega-noncomputable`)。

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
- `Omega.lean` — P9 (`chaitinOmega` 定義 + `≤ 1` / `0 <` / `≠ ⊤` + interpret モード入口 + prefix invariance +
  **prefix K の**非計算性)。Ω 自体の非計算性は park slug の新ファイル (起票時に決める) へ
- `Levin.lean` — P8 (等号 crux、flagship)
- `SufficientStatistic.lean` — P10 (KSS / MDL、stretch)

各ファイル追加時に `InformationTheory.lean` へ import 行を登録。`private` helper を共有する sub-module は
同一ファイルに置く (file-scoped `private`)。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正時。決着済 entry は削除 (git が履歴)、active な判断のみ残す。

(#1 = 単一壁 slug の撤回は gateway atom / P7 / P9 の通過で決着 ⟹ §settled facts に集約、判断ログからは畳んだ。
番号は他文書参照を壊さないため振り直さない。)

2. **U_pf は第 1 波 `universalEval` の拡張でなく別機械 (active、inventory 採用)**: literal `false::bs` が前置閉で
   prefix-free でないため。再利用は interpret 委譲機構のみ。§定義形の設計判断。
3. **P8 等号方向を crux として保守的に (active、under-estimation ガード)**: inventory の P8 ✖→△ は着手前見積。
   Kraft は符号存在の必要条件しか与えず、P_U 質量からの prefix program 構成 (Kraft 逆向き) は self-build。
   R-W2b 発動公算 = 中。gateway/P7/P9 が軽く通ったことを P8 の軽さの根拠に読み替えない。
4. **Ω 自体の非計算性は park、順序を後ろへ (active、orchestrator 決定)**: P9 で着地したのは **prefix K の
   非計算性**であり Ω の非計算性ではない。Ω 非計算性は実数計算可能性の自前定式化 + U_pf の partrec 性を要する
   (§settled facts の loogle 実測、候補定式化 3 つも同節) ⟹ **scope から落とすのではなく順序を後ろへ**:
   flagship の P8 を先に取り、P8 / P10 の後に budget が残れば回収する。park slug
   `plan:kolmogorov-w2-omega-noncomputable`。
5. **P8 着手ゲート = prefix invariance の strength diff を先に 1 回通す (active)**: in-tree の
   `prefix_invariance` は `K(x) ≤ 2 * |q| + b` (機械の単進長さ前置に由来する線形係数 2) で、教科書の加法的
   prefix invariance の **weaker relative**。Berry (P9) には十分だが Levin 等号にはそのまま使えない ⟹
   §Phase P8 ⚠️ の 3 択 (自己限定済み記述を渡す / 機械 def 変更 + ripple / factor-2 版へ言い換え) を
   実装着手前に決める。factor-2 版を教科書 Levin と称するのは name laundering で禁止。

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
- [x] Phase P8 — prefix K と普遍確率の **factor-2 関係** ✅ (`Levin.lean`、`6861eb14`/`be6d1f7f`/`07acd1c0`)
      — **教科書の加法版 Levin 定理は証明していない** (この機械では真偽不明 ⟹ plan 段 park、§Phase P8)
- [ ] Phase P9 — Chaitin Ω (§14.9) 🚧 Ω 収束 + prefix K 非計算性は着地 (`Omega.lean`、`4f55f459`/`07057aa1`)、
      **Ω 自体の非計算性のみ未了** → park (`plan:kolmogorov-w2-omega-noncomputable`)
- [ ] Phase P10 — Kolmogorov 十分統計量 (§14.12、stretch、最重量) 📋 ← **次のマイルストーン**

**第 2 波の control state (cold-read 用)**: gateway atom は通過 ⟹ make-or-break は解消し **R-W2a は回避**
(自己限定符号が実際に組めた)。P7 は DONE。**P8 は factor-2 関係として着地** —
`-log₂ P_U(x) ≤ K(x) ≤ 2·(-log₂ P_U(x)) + 1` が第 2 波の頂点であり、**教科書の加法版
`|K(x) + log₂ P_U(x)| ≤ c` は証明していない**。加法版はこの機械では真偽不明ゆえコード側に `sorry` を置かず
**plan 段のみで park** (§residual slug 方針、後継は加法的普遍 prefix 機械の構成)。P9 は Ω 収束
(`chaitinOmega_le_one`) + **prefix K の非計算性** (`prefixComplexity_not_computable`) まで着地し、
**Ω 自体の非計算性だけが未了** (park、下記 slug 表)。**次のマイルストーンは P10** = 解析壁でなく最重量の
定義量 (250–500 行) = 撤退候補で DAG 末尾の stretch のまま。`wall:` を打つ先は現状無い (genuine 壁判定は
実測後に初めて行う)。途中 sorry の残置状況は plan に焼き込まず
`rg "@residual" InformationTheory/Shannon/Kolmogorov/` で都度確認する。

## ゴール / Scope

**最終到達点 (flagship、P8 着地により訂正)**: 当初は Levin 符号化定理の**加法版**
`|-log₂ P_U(x) - K(x)| ≤ c` (CT 2nd ed §14.6) を prefix 塔の頂点に据え、headline 名も `levin_coding_theorem` と
予定していた。**この目標地点を訂正する** — 第 2 波の頂点は **factor-2 関係**
`-log₂ P_U(x) ≤ K(x) ≤ 2·(-log₂ P_U(x)) + 1` であり、`@[entry_point]` headline は上半分の
`prefixComplexity_le_two_mul_neg_logb_universalProb` (下半分は P7 の `neg_logb_universalProb_le_prefixComplexity`)。
訂正の理由: 加法版は**加法的普遍 prefix 機械** (任意の prefix 機械を定数コストでシミュレートできる機械) についての
主張であり、in-tree の `prefixUniversalEval` はそれではない (§Phase P8 の 3 択判定)。**当初の野心は削除ではなく
後継ルートへ移す** — 別の機械を建てる必要があり、leg でなく別 moonshot 級 (§residual slug 方針)。

**In (第 2 波)**: gateway atom (prefix-free 機械 U_pf + K + P_U + Kraft 1 回適用) → **P7 普遍確率下界** (CT 14.6.1)
→ **P8 factor-2 関係** (flagship、上記の訂正後の形) → **P9 Chaitin Ω** (§14.9、収束 + 非計算性。**Ω 自体の
非計算性は park**、§Phase P9) → **P10 Kolmogorov 十分統計量** (§14.12、stretch)。P10 はユーザー確定で本 moonshot の最終 Phase に含めるが、honest に「最重量の
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
   ┌──── P7 普遍確率下界 ✅ ────┐  P_U(x) ≥ 2^{-K(x)} + 対数形 (factor-2 関係の下半分)
   │                          │
   ▼                          ▼
P9 Chaitin Ω 🚧              P8 factor-2 関係 ✅ (flagship、`Levin.lean`)
 収束 ✅ (chaitinOmega_le_one)   K(x) = 2·m(x) + 1 (構造恒等式) + P_U(x) ≤ 2^{-m(x)} (数え上げ)
 prefix K 非計算性 ✅            ⟹ K(x) ≤ 2·(-log₂ P_U(x)) + 1、P7 と合流して両側 factor-2
 Ω 自体の非計算性 → park        加法版は加法的普遍機械を要する ⟹ 後継 moonshot へ park (コード側 sorry 無し)
   │                          │
   └────────┬─────────────────┘
            ▼
        P10 Kolmogorov 十分統計量 (§14.12、stretch、最重量定義量 250–500 行、撤退候補) ← 次のマイルストーン
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
**gateway-atom-first で実測するまで壁/非壁を確定しない** (CLAUDE.md「not-a-wall を額面で受けない」)。**P8 で
このガードが最も効いた**: 実装は見積の下側 (~245 行) で収まり Shannon-Fano-Elias の逆向き構成すら要らなかったが、
軽かったのは**着地した命題が当初掲げた加法版ではなく factor-2 版**だからである。着手前に prefix invariance の
2 倍係数 (weaker relative) の strength diff を 1 回通したことで、加法版が「まだ証明していない命題」ではなく
「この機械では真偽不明の命題」だと判明した (§Phase P8)。⟹ **行数が予算内に収まったことを、命題が当初予定どおり
入った証拠に読み替えないこと**。残る P10 も同じ規律で扱う (最重量なのは定義量 = 選択 (big) であって解析壁ではない、
という見立て自体を実測で検算する)。

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
- **並走レーン**: 残る並走可能レーンは P10 (stretch) と Ω 自体の非計算性 (park slug、第 1 波 halting 資産のみ依存)。
- **第 1 波資産の signature 変更なし**: 第 2 波は第 1 波資産を read-only 消費する新規定義群 ⟹ 第 1 波側の
  consumer ripple 解析は不要。**第 2 波内部の `prefixUniversalEval` も P8 では触らなかった** (出口 (ii) を採らず、
  P8 は `tsum_inv_two_pow_length_le_one` の一般化 = 旧名を署名同一 wrapper で残す形で済んだ ⟹ ripple 0)。
  実測済 consumer 表は後継 plan の見積用に §Phase P8 に残す。

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

### Phase P8 — prefix K と普遍確率の factor-2 関係 (flagship `@[entry_point]`) ✅

- **状態**: DONE (`Levin.lean` ~245 行 / 16 decl、commits `6861eb14` + honesty ゲート `be6d1f7f` +
  style ゲート `07acd1c0`)。見積 200–400 行の下側。`InformationTheory.lean` へ import 登録済。
- **着地した成果物** (いずれも仮説なし。署名は `scripts/sig_view.ts` で都度確認):
  ```lean
  noncomputable def payloadComplexity (x : ℕ) : ℕ         -- 最短 payload 長 m(x)
  def padDelimit (m : ℕ) (d : List Bool) : List Bool      -- 単進 run を offset 分短縮したラッパ
  theorem prefixComplexity_eq_two_mul_payloadComplexity_add_one (x : ℕ) :
      prefixComplexity x = 2 * payloadComplexity x + 1
  theorem universalProb_le_two_pow_neg_payloadComplexity (x : ℕ) :
      universalProb x ≤ (2 : ℝ≥0∞)⁻¹ ^ payloadComplexity x
  @[entry_point] theorem prefixComplexity_le_two_mul_neg_logb_universalProb (x : ℕ) :
      (prefixComplexity x : ℝ) ≤ 2 * (-Real.logb 2 (universalProb x).toReal) + 1
  ```
  P7 の `neg_logb_universalProb_le_prefixComplexity` と合流して **両側 factor-2 関係**
  `-log₂ P_U(x) ≤ K(x) ≤ 2·(-log₂ P_U(x)) + 1` = 第 2 波の頂点。当初案の `0 < universalProb x →` ガードは
  予定どおり不要だった (P7 下界 + `ENNReal.pow_pos`、§定義形「対数形の型」)。
- **証明機構 (SFE ではなく数え上げ)**: x を出力する program は長さ ≥ m(x) の payload に単射で入り、その payload を
  `padDelimit m` で巻き直すと質量が `2^{-m(x)}` × (prefix-free 集合上の Kraft 可算和) の形で露出する。⟹
  **Shannon-Fano-Elias (算術符号) の逆向き構成は要らなかった**。`padDelimit m` は `m ≠ 0` では機械の program に
  ならない (単進前置が payload 長を下回り受理ガードが弾く) が、必要なのは像の prefix-free 性だけ。
- **enabling 資産の一般化 (ripple 0)**: `tsum_inv_two_pow_length_le_one` を
  **`PrefixFree.tsum_inv_two_pow_length_le_one`** (任意 prefix-free 集合 + 空語なし。有限形は `PrefixFree.kraft`)
  に一般化。旧名は署名同一の wrapper として残したので `Omega.lean` / `UniversalProbability.lean` の consumer は
  無変更で通った。
- **strength diff ゲートの判定 (着手前の 3 択に決着、textbook-object strength diff)**: 教科書の prefix invariance は
  加法的 `K(x) ≤ K_A(x) + c_A` だが in-tree は `K(x) ≤ 2·|q| + b` (`Omega.lean`) の **weaker relative**。3 択の帰結:
  1. **(i) 自己限定済み記述を渡して加法定数に落とす = 困難ではなく原理的に不可能**。`dom_imp_mem_range` が受理
     program を `Set.range selfDelimit` に閉じ込め、`selfDelimit_length` が `|selfDelimit d| = 2·|d| + 1` を与える
     ⟹ `prefixComplexity_eq_two_mul_payloadComplexity_add_one` が `K = 2·m + 1` を **恒等式として**主張する。
     記述をどう符号化して渡しても加法定数は回復しない (2 倍は機械の def の性質)。
  2. **(ii) 機械 def 変更 = 後継ルート**。「符号自身の prefix-free 性が parse 境界を与える」モードこそ
     **加法的普遍 prefix 機械**に要るものだが、任意の `Nat.Partrec.Code` 上で dovetail 先着順フィルタを回して機械を
     建てる必要がある (生の `Code` の `List Bool` 入力上の停止集合は prefix-free でない) ⟹ leg ではなく別
     moonshot 級の構成。実測 ripple 表 (下) はこの後継の見積用にそのまま残す。
  3. **(iii) 採用したが「言い換え」から「証明」へ格上げ**。flagship を factor-2 版に言い換えるだけで済ませず、
     **実在する機械に対して両側の真の bound を証明**した。
- **(ii) を後継 plan で選ぶ場合の ripple (`scripts/dep_consumers.sh` 実測、P8 着手前の値)**:

  | target | direct consumers | 内訳 (file) |
  |---|---|---|
  | `prefixUniversalEval` | **21 decl / 3 file** | `PrefixMachine.lean` 10 / `Omega.lean` 9 / `UniversalProbability.lean` 2 |
  | `prefixComplexity` | **12 decl / 3 file** | `Omega.lean` 9 / `PrefixMachine.lean` 1 / `UniversalProbability.lean` 2 |
  | `universalProb` | **3 decl / 1 file** | `UniversalProbability.lean` 3 |

  import closure も同じ 3 ファイル (+ root) なので、機械の def 変更の影響は第 2 波内部に閉じる (第 1 波 / 他家系に
  波及しない)。ただし `prefixUniversalEval` を触ると `chaitinOmega` の値そのものが変わる = P9 の着地物 (収束 3 本 +
  非計算性) の**再証明が要る**点を見積に入れること。`Levin.lean` の 16 decl も同じ理由で作り直しになる。
- **加法版を「コード側の sorry」にしなかった理由 (honesty)**: 教科書の加法符号化定理
  `|K(x) + log₂ P_U(x)| ≤ c` (CT §14.6) は **`sorry + @residual(plan:kolmogorov-w2-levin)` としても置いていない**。
  この機械に対しては**未証明ではなく真偽不明** — x を出力する全 program の総質量が最短 1 本の質量の定数倍に収まるか、
  という機械固有の研究水準の問いになる。**偽かもしれない命題に `@residual` を貼ること自体が defect** ⟹ park は
  plan 段のみ (§settled facts の human-judgment entry が決着条件を持つ)。`Levin.lean` の module docstring は
  「加法定理は加法的普遍 prefix 機械についての主張でありここでは主張しない」を明示している。
- **proof-log**: yes を指定していたが**未取得** (`docs/proof-logs/` に該当ファイル無し、`rg` 実測)。数え上げ機構が
  SFE 逆向き構成を置き換えた点は method 資産としての価値があるので、回収するなら後続 leg で。

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
- **R-W2b** (P8 等号 crux が 400 行超で発散 → 最小成果先取り): **未発動 — 最小成果を上回って着地**。「P8 全体を
  park」の意味では発動していない: P8 は ~245 行で proof-done し、退避出口
  `sorry + @residual(plan:kolmogorov-w2-levin)` は使わなかった (コード側に本 slug の `sorry` は 0)。ただし着地形は
  factor-2 版であり、**教科書の加法版だけが後継ルートへ park** (§residual slug 方針)。factor-2 版を教科書 Levin と
  称さない禁止事項は恒久的に有効 (name laundering)。slug は他文書参照のため register に残す。

**判定 (現時点)**: R-W2a 回避済、R-W2b 未発動 (P8 は factor-2 形で proof-done、最小成果を超過)。残る撤退ラインは
P10 の Phase 全体撤退候補 (§Phase P10) のみ。

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
| `kolmogorov-w2-levin` | `kolmogorov-w2-levin-plan.md` (未作成) | **加法版 Levin 定理**。**plan 段の park で、対応する `sorry` はコード側に 0 本** (下記) |
| `kolmogorov-w2-kss` | `kolmogorov-w2-kss-plan.md` | P10 十分統計量 |

`kolmogorov-w2-omega-noncomputable` は **`wall:` ではなく `plan:`** — 実数計算可能性が Mathlib に無いのは
「解析が難しい (hard)」ではなく「定式化と自作インフラを選ぶ (big)」側だからである (§settled facts の loogle 実測)。

**`kolmogorov-w2-levin` は「コード側 `sorry` を持たない park slug」**という特殊形である (P8 着地後)。factor-2 版は
proof-done で入り、残る加法版 `|K(x) + log₂ P_U(x)| ≤ c` は**この機械では真偽不明**ゆえ `@residual` を貼れない
(偽かもしれない命題に貼るのが defect、§Phase P8)。⟹ 本 slug は plan 段の park 記録としてのみ生き、後継 plan が
負うのは**証明ではなく構成**: 加法的普遍 prefix 機械 (任意の `Nat.Partrec.Code` に対する dovetail 先着順フィルタで
prefix-free な停止集合を作り出す機械) を建て、その機械の K に対して加法版を述べ直す。付随して `prefixUniversalEval`
を差し替えるなら §Phase P8 の ripple 表 (21/12/3 decl) + P9 着地物の再証明を負う。

**`wall:` を打つ先は現状無い** — 加法版も「新しい機械を建てる」= 選択 (big) であって Mathlib 不在の解析 (hard)
ではない。genuine `wall:` が実測で現れたらその時点で `docs/audit/audit-tags.md` の Wall register に追記する。

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

- **claim (confidence = `machine`)**: 着地した機械では **`prefixComplexity x = 2 * payloadComplexity x + 1` が
  恒等式**として成り立つ (`≤` ではなく `=`)。受理 program が `Set.range selfDelimit` に閉じ、
  `|selfDelimit d| = 2·|d| + 1` であることが源。
  - 再検証: `lake env lean InformationTheory/Shannon/Kolmogorov/Levin.lean` +
    `#print axioms InformationTheory.Kolmogorov.prefixComplexity_eq_two_mul_payloadComplexity_add_one`
  - last-verified: `07acd1c0`
  - **含意**: 加法版 Levin 定理は「記述の渡し方の設計」では取れない (§Phase P8 出口 (i) を**不可能**と判定した根拠)。
    2 倍は証明の緩さではなく機械の def の性質。
- **claim (confidence = `machine`)**: **`universalProb x ≤ (2 : ℝ≥0∞)⁻¹ ^ payloadComplexity x`** (数え上げ上界)。
  x を出力する program が長さ ≥ m(x) の payload に単射で入ることと `padDelimit m` 像の Kraft 可算和から出る。
  - 再検証: 上と同じ `lake env lean` +
    `#print axioms InformationTheory.Kolmogorov.universalProb_le_two_pow_neg_payloadComplexity`
  - last-verified: `07acd1c0`
  - **含意**: Shannon-Fano-Elias の逆向き構成は factor-2 版には不要 (P8 が見積下側で収まった理由)。
- **claim (confidence = `human-judgment` ⟹ 低信頼、独立 pivot で再確認せよ)**: 加法版
  `|K(x) + log₂ P_U(x)| ≤ c` の **この機械 (`prefixUniversalEval`) における真偽は未決**。上半分を出すには
  「x を出力する全 program の総質量が最短 1 本の質量の定数倍以内」が要り、機械固有の研究水準の問いになる。
  - **決着させるもの (どちらかで閉じる)**: (a) 総質量が最短質量の定数倍を超える x の族を 1 つ構成する ⟹ この機械では
    **偽**が確定し、後継 plan は機械の建て替え一本になる。(b) 加法的普遍 prefix 機械 (§Phase P8 出口 (ii)) を建て、
    **そちらの K に対して**加法版を証明する ⟹ 元の機械での真偽を問わずに教科書命題が入る。
  - **コード側に `sorry` を置いていない**のはこの未決性ゆえ (偽かもしれない命題に `@residual` を貼らない)。
    確度の低い判定なので、後継着手時は (a) の反例探索を先に 1 回試すこと。

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
- `Levin.lean` — P8 (`payloadComplexity` / `padDelimit` + factor-2 関係の flagship)
- `SufficientStatistic.lean` — P10 (KSS / MDL、stretch)

各ファイル追加時に `InformationTheory.lean` へ import 行を登録。`private` helper を共有する sub-module は
同一ファイルに置く (file-scoped `private`)。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正時。決着済 entry は削除 (git が履歴)、active な判断のみ残す。

(#1 = 単一壁 slug の撤回は gateway atom / P7 / P9 の通過で決着 ⟹ §settled facts に集約。#3 = P8 を crux として
保守的に扱う判断、#5 = P8 着手ゲート (strength diff) はいずれも P8 の着地で決着 ⟹ §Phase P8 / §settled facts /
§Approach「under-estimation ガード」に集約。判断ログからは畳んだ。番号は他文書参照を壊さないため振り直さない。)

2. **U_pf は第 1 波 `universalEval` の拡張でなく別機械 (active、inventory 採用)**: literal `false::bs` が前置閉で
   prefix-free でないため。再利用は interpret 委譲機構のみ。§定義形の設計判断。
4. **Ω 自体の非計算性は park、順序を後ろへ (active、orchestrator 決定)**: P9 で着地したのは **prefix K の
   非計算性**であり Ω の非計算性ではない。Ω 非計算性は実数計算可能性の自前定式化 + U_pf の partrec 性を要する
   (§settled facts の loogle 実測、候補定式化 3 つも同節) ⟹ **scope から落とすのではなく順序を後ろへ**:
   flagship の P8 を先に取り、P8 / P10 の後に budget が残れば回収する。park slug
   `plan:kolmogorov-w2-omega-noncomputable`。
6. **P8 は factor-2 形で着地、加法版は plan 段のみで park (active、strength diff ゲートの決着)**: 着手前ゲートの
   3 択は (i) **原理的に不可能** (`K = 2·m + 1` が恒等式) / (ii) 加法的普遍機械の構成 = 別 moonshot 級の後継ルート /
   (iii) 採用のうえ「言い換え」から「証明」へ格上げ、で決着した (§Phase P8)。flagship は
   `prefixComplexity_le_two_mul_neg_logb_universalProb` + P7 下界 = 両側 factor-2 で、§ゴールの目標地点も訂正済
   (当初の加法版の野心は削除せず後継ルートへ移した)。**加法版はコード側に `sorry` を置かない** — この機械では
   真偽不明であり、偽かもしれない命題に `@residual` を貼るのは defect ⟹ park は plan 段のみ、決着条件は
   §settled facts の human-judgment entry が持つ。factor-2 版を教科書 Levin と称するのは恒久的に禁止。

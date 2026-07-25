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
      — **教科書の加法版 Levin 定理は証明していない** (この機械では真偽不明 ⟹ 後継 scope、§Phase P8)
- [x] Phase P9 — Chaitin Ω (§14.9) ✅ (`Omega.lean`、`4f55f459`/`07057aa1`)。
      **Ω 自体の非計算性 (後継 scope) も closure** ✅ → 子 plan
      [`kolmogorov-w2-omega-noncomputable-plan.md`](kolmogorov-w2-omega-noncomputable-plan.md)
      (N0–N5 全段 proof-done、`chaitinOmega_not_computable` は仮説ゼロ。撤退ライン発動 0)
- [x] Phase P10 — Kolmogorov 十分統計量 (§14.12) ✅ (`SufficientStatistic.lean`、
      `ffefd9d8`/`ec2f6eba`/`56d6a773`/`d6cc3062`) → 在庫 [`kolmogorov-w2-p10-inventory.md`](kolmogorov-w2-p10-inventory.md)

**第 2 波の control state (cold-read 用)**: **第 2 波は達成** — M0 / gateway atom / P7 / P8 / P9 / P10 が全て着地した。
頂点は P8 の factor-2 関係 `-log₂ P_U(x) ≤ K(x) ≤ 2·(-log₂ P_U(x)) + 1`、DAG 末尾の P10 (§14.12 十分統計量) も
`SufficientStatistic.lean` で着地し、在庫が唯一の退避候補としていた crux (機械の自己シミュレーション) まで
退避なしで閉じた。**後継 scope 2 件のうち (b) Ω 自体の非計算性も closure** (子 plan、`chaitinOmega_not_computable`
が仮説ゼロで proof-done) ⟹ **残る後継 scope は (a) 加法版 Levin 定理 1 件のみ** = 別の機械 (加法的普遍 prefix 機械)
の構成 (`plan:kolmogorov-w2-levin`、子 plan 未作成、コード側 `sorry` 0)。
`wall:` を打つ先は最後まで現れなかった。
sorry / residual の残置状況は plan に焼き込まず `rg "@residual" InformationTheory/Shannon/Kolmogorov/` で都度確認する。

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
→ **P8 factor-2 関係** (flagship、上記の訂正後の形) → **P9 Chaitin Ω** (§14.9、収束 + prefix K 非計算性)
→ **P10 Kolmogorov 十分統計量** (§14.12)。

**達成判定 (2026-07-25)**: **In の 5 項すべてが着地 ⟹ 第 2 波は達成**。P7 / P8 / P9 / P10 の着地物と commit は
§Phase 詳細。**後継 scope は「未達」ではなく「別の object を建てる」話**なので区別する (2 件のうち 1 件は closure):

| 後継 scope | 状態 | 何が要る / 何が入ったか | slug |
|---|---|---|---|
| Ω 自体の非計算性 | **✅ closure** (2026-07-25) | 実数計算可能性の述語 `IsComputableENNReal` を自前で定義し Chaitin 論法で否定 → 子 plan [`kolmogorov-w2-omega-noncomputable-plan.md`](kolmogorov-w2-omega-noncomputable-plan.md) (N0–N5、撤退ライン発動 0) | `plan:kolmogorov-w2-omega-noncomputable` |
| 加法版 Levin `\|K(x) + log₂ P_U(x)\| ≤ c` | 📋 **唯一の残 scope** (子 plan 未作成) | この機械では真偽不明 ⟹ **加法的普遍 prefix 機械の構成** (別 moonshot 級) | `plan:kolmogorov-w2-levin` |

**残 scope はコード側に対応する `sorry` を持たない** (真偽不明ゆえ `@residual` を貼れない) ⟹ park は plan 段のみ。

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
P9 Chaitin Ω ✅              P8 factor-2 関係 ✅ (flagship、`Levin.lean`)
 収束 ✅ (chaitinOmega_le_one)   K(x) = 2·m(x) + 1 (構造恒等式) + P_U(x) ≤ 2^{-m(x)} (数え上げ)
 prefix K 非計算性 ✅            ⟹ K(x) ≤ 2·(-log₂ P_U(x)) + 1、P7 と合流して両側 factor-2
 Ω 自体の非計算性 ✅ (子 plan)   加法版は加法的普遍機械を要する ⟹ 唯一の残 scope (コード側 sorry 無し)
  `OmegaNoncomputable.lean`   │  (P10 は P8 のみを消費、P9 とは独立)
                              ▼
        P10 Kolmogorov 十分統計量 ✅ (§14.12、`SufficientStatistic.lean` 594 行)
        two-part 符号 + MDL の headline 2 本 + 自己シミュレーション crux まで proof-done
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
入った証拠に読み替えないこと**。

**P10 での検算結果 (両方向に効いた)**: 「最重量なのは定義量 = 選択 (big) であって解析壁ではない」という見立ては
実測で維持された (`wall:` 0 件で closure)。一方 **行数は見積 250–500 に対し実績 594 = 上振れ**し、重さの所在も
定義群ではなく **crux (bit codec の `Primrec` 化 + 機械の自己シミュレーション)** に寄っていた。⟹ 見積下振れ
(P8) と上振れ (P10) の両方を実測が是正しており、**行数見積は着地の可否を予言しない**という同じ結論に落ちる。
そして P10 の係数会計は P8 と同じ構造 — 教科書形の係数 1 は取れず `4·⌈log₂|S|⌉` を**定義側に**置く (§Phase P10)。

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
| `ComputablePred.halting_problem` | `Mathlib/Computability/Halting.lean:65` | Ω 非計算性の前哨 atom (`PrefixComputability.lean`) の矛盾先 (第 1 波 P5 と同弾) |

**`entropy` (`Bridge.lean:40`) は第 2 波の依存ではない** (当初は P10 の H(X) 項として挙げていた)。CT §14.12 の
対象は 1 本の文字列 `x` についての量で測度が出てこないため — P10 在庫 §F の判定であり、着地した
`SufficientStatistic.lean` も `Bridge` を import していない (child = 在庫が SoT)。

### 実装原則

- **Skeleton-driven**: 各 Phase は全補題を `:= by sorry` で建て type-check done を確認してから 1 sorry ずつ充填。
  inventory §着手 skeleton (`PrefixMachine.lean` 出だし) がそのまま Gateway atom の skeleton。
- **並走レーン**: 第 2 波内に残るレーンは無い。後継 scope も Ω 非計算性が closure し、残るのは加法版 Levin
  (機械の建て替え) 1 レーンのみ。
- **第 1 波資産の signature 変更なし**: 第 2 波は第 1 波資産を read-only 消費する新規定義群 ⟹ 第 1 波側の
  consumer ripple 解析は不要。**第 2 波内部の `prefixUniversalEval` も P8 では触らなかった** (出口 (ii) を採らず、
  P8 は `tsum_inv_two_pow_length_le_one` の一般化 = 旧名を署名同一 wrapper で残す形で済んだ ⟹ ripple 0)。
  実測済 consumer 表は後継 plan の見積用に §Phase P8 に残す。

---

## Phase 詳細

各 Phase: 依存 / 成果物 (signature 略式) / 見積行数 / proof-log / 撤退ライン。

### Phase M0 — Mathlib API 在庫調査 ✅

DONE。[`kolmogorov-w2-inventory.md`](kolmogorov-w2-inventory.md) が SoT (Kraft 既存の overturn +
§Key-preconditions box)。P10 分は別在庫 [`kolmogorov-w2-p10-inventory.md`](kolmogorov-w2-p10-inventory.md)。
proof-log: no (調査 Phase)。

### Gateway atom — prefix-free 機械 U_pf + K + P_U + Kraft 1 回適用 ✅

DONE (`PrefixMachine.lean`、`537c5ab8` + ゲート `a448b313`)。**R-W2a 回避** — 自己限定 literal 符号
(単進長さ前置 `selfDelimit`) が実際に組め Kraft 接続まで通った ⟹ make-or-break 解消。提供 API は
§Approach「gateway atom = 第 2 波の礎石」。proof-log: yes (取得済)。

### Phase P7 — 普遍確率下界 (CT 14.6.1) ✅

DONE (`UniversalProbability.lean`、`16ce3108` + ゲート `4303c4b6`、実測 ~80 行 = 見積 60–120 行の下側)。
`universalProb_ge_two_pow_neg_prefixComplexity` (`@[entry_point]`) / `universalProb_le_one` /
`neg_logb_universalProb_le_prefixComplexity` の 3 本、いずれも仮説なし。3 本目が factor-2 関係の下半分そのもので、
`0 < universalProb x` を仮説に持たない (K が total ⟹ 全 x で正) ため P8 は上半分だけを残した。proof-log: no。

### Phase P8 — prefix K と普遍確率の factor-2 関係 (flagship `@[entry_point]`) ✅

- **状態**: DONE (`Levin.lean` ~245 行 / 16 decl、`6861eb14` + ゲート `be6d1f7f` / `07acd1c0`)。見積 200–400 行の
  下側。headline `prefixComplexity_le_two_mul_neg_logb_universalProb` (`@[entry_point]`、仮説なし) が P7 下界と
  合流して **両側 factor-2 関係** `-log₂ P_U(x) ≤ K(x) ≤ 2·(-log₂ P_U(x)) + 1` = 第 2 波の頂点。支える 2 本は
  `prefixComplexity_eq_two_mul_payloadComplexity_add_one` (構造恒等式) と
  `universalProb_le_two_pow_neg_payloadComplexity` (数え上げ)。**Shannon-Fano-Elias の逆向き構成は不要だった**。
- **strength diff ゲートの判定 (着手前の 3 択に決着、後継ルートの根拠なので保持)**: 教科書の prefix invariance は
  加法的 `K(x) ≤ K_A(x) + c_A` だが in-tree は `K(x) ≤ 2·|q| + b` (`Omega.lean`) の **weaker relative**。
  1. **(i) 自己限定済み記述を渡して加法定数に落とす = 困難ではなく原理的に不可能**。受理 program が
     `Set.range selfDelimit` に閉じ `|selfDelimit d| = 2·|d| + 1` ⟹ `K = 2·m + 1` は**恒等式**であり、記述の
     符号化をどう変えても加法定数は回復しない (2 倍は機械の def の性質)。
  2. **(ii) 機械 def 変更 = 後継ルート**。「符号自身の prefix-free 性が parse 境界を与える」モードこそ
     **加法的普遍 prefix 機械**に要るが、任意の `Nat.Partrec.Code` 上で dovetail 先着順フィルタを回して機械を
     建てる必要がある (生の `Code` の `List Bool` 入力上の停止集合は prefix-free でない) ⟹ leg ではなく別
     moonshot 級の構成。実測 ripple 表 (下) はこの後継の見積用にそのまま残す。
  3. **(iii) 採用のうえ「言い換え」から「証明」へ格上げ** — 実在する機械に対して両側の真の bound を証明した。
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
  plan 段のみ (§settled facts の human-judgment entry が決着条件を持つ)。
- **proof-log**: yes を指定していたが**未取得**。数え上げ機構が SFE 逆向き構成を置き換えた点は method 資産として
  価値があるので、回収するなら後続 leg で。

### Phase P9 — Chaitin Ω (§14.9) ✅ 後継 scope まで含めて closure

- **状態**: DONE (`Omega.lean`、`4f55f459` + ゲート `07057aa1`)。**入った**: `chaitinOmega` 定義 + 収束
  `chaitinOmega_le_one` (`@[entry_point]`) / `chaitinOmega_pos` / `chaitinOmega_ne_top`、interpret モード入口
  (`prefixInterpretProg` / `prefixUniversalEval_interpret`)、prefix invariance (`K(x) ≤ 2·|q| + b`、⚠️ P8 節)、
  **prefix K の非計算性** `prefixComplexity_not_computable` (`@[entry_point]`、Berry 論法)。
- **Ω 自体の非計算性 = 後継 scope も closure ✅ (2026-07-25)**: P9 波内で着地したのは **K の非計算性であって
  Ω の非計算性ではない** (別 object) ため子 plan へ切り出したが、その子
  [`kolmogorov-w2-omega-noncomputable-plan.md`](kolmogorov-w2-omega-noncomputable-plan.md) が
  **N0–N5 全段 proof-done で closure**。着地物 = `PrefixComputability.lean` (前哨 gateway atom、`4efc230d`) +
  `OmegaNoncomputable.lean` (`cea4d851`〜`7ea3eb26` + 2 ゲート)、headline
  `chaitinOmega_not_computable : ¬ IsComputableENNReal chaitinOmega` は**仮説ゼロ**。撤退ライン発動 0。
  **この object の control state / 定義形 / settled facts は子が SoT** — 親は DAG / slug 表のリンクだけを同期する。
  「algorithmically random」の主張も同 slug で扱う。
- **P10 が着手コストを下げた経路 (記録)**: 子の前哨 atom は P10 の crux 用に入った computability infra
  (`SufficientStatistic.lean` の bit codec `Primrec` 群 + `decodePayload_partrec`) をそのまま消費して
  `prefixUniversalEval_partrec` / `prefixUniversalEval_dom_not_computablePred` を建てた。子 N0 が追加したのは
  `payloadDispatch_primrec` (`SufficientStatistic.lean:347`、本体移設ゆえ署名不変・ripple 0) のみ。
  **後継 scope `kolmogorov-w2-levin` (機械の建て替え) も同じ infra を出発点にできる**。
- **proof-log**: no (子側の N0 / N3 分は未取得、子 §判断ログ #6)。

### Phase P10 — Kolmogorov 十分統計量 (§14.12) ✅

- **状態**: DONE (`SufficientStatistic.lean` 594 行 / 56 decl、`ffefd9d8` + 補追 `ec2f6eba` / `56d6a773` +
  style ゲート `d6cc3062`)。見積 250–500 行に対し **実績 594 行 = 上振れ** (重さは定義群でなく crux 側、
  §Approach「under-estimation ガード」)。在庫 = [`kolmogorov-w2-p10-inventory.md`](kolmogorov-w2-p10-inventory.md)。
- **依存**: prefix K (Gateway atom) + `payloadComplexity` / `prefixComplexity_eq_two_mul_payloadComplexity_add_one`
  (P8 `Levin.lean`) のみ。**第 1 波 `entropy` は依存しない** (§Approach 末尾、在庫 §F が SoT)。**P9 も依存しない** —
  在庫は `prefix_invariance` を使う段で `Omega` を import する想定だったが、実装は payload 世界の
  `payload_invariance` を自前で建てたため `Omega` を import していない (import 行と `rg` で確認)。
- **着地した成果物** (署名は `scripts/sig_view.ts` で都度確認):
  - **headline 2 本 (`@[entry_point]`)**: `prefixComplexity_le_twoPartLength` (two-part 符号の達成可能性) /
    `mdlComplexity_sub_prefixComplexity_le` (MDL 原理、両側)
  - **定義 6 本**: `modelCode` / `modelComplexity` / `twoPartLength` / `mdlComplexity` / `structureFunction` (ℕ∞ 値) /
    `IsSufficientStatistic` (c を明示引数)
  - **構造関数系**: `structureFunction_antitone` / `structureFunction_zero` (k=0 で `⊤`) /
    `structureFunction_eq_zero_of_singleton_budget`、MDL 系 `mdlComplexity_spec` / `mdlComplexity_le_of_mem`
  - **十分統計量の witness**: `exists_isSufficientStatistic_singleton` (`∃ c, ∀ x, IsSufficientStatistic c x {x}`)、
    supporting `modelComplexity_singleton_le`
  - **crux (在庫が唯一の退避候補としていた本体)**: `payloadComplexity_two_part_le` = 機械の自己シミュレーション。
    bit codec の `Primrec` 化 (`encodeNat_primrec` / `decodeNat_primrec` / `parseUnary_primrec`) +
    `Nat.Partrec.Code.eval_part` 経由の `decodePayload_partrec` で組み、**退避なしで closure**。
    副産物 `payload_invariance` (`:411`) は payload 世界の**加法的** invariance (`≤ q.length + b`) で、後継 scope
    (加法的普遍機械) の見積に効く。
- **係数会計 (honest scope、在庫 §Honest scope call (C1))**: 教科書の `K(x) ≤ K(S) + log|S| + O(1)` は**係数 1 では
  取れない** (`K = 2·m + 1` が恒等式ゆえ index 項に 2×2 が乗る) ⟹ **`4 * Nat.clog 2 S.card` を `twoPartLength` の
  定義側に埋め込む**ことで headline を加法定数のみの汚染に落とした。**教科書の two-part 不等式と同一視して命名
  しない**のは P8 の name laundering 禁止の再演 (module docstring が明示)。
- **proof-log**: yes を指定していたが**未取得** (P8 と同じ扱い、回収するなら後続 leg で)。
- **撤退ライン**: **未発動** (§撤退ライン)。

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

- **R-W2c** (在庫が提案した P10 の crux 単独 park = `payloadComplexity_two_part_le` を共有 sorry 補題として残し、
  定義群 + 構造的定理だけ type-check done で着地させる): **未発動** — crux 本体が proof-done で閉じたため
  縮退出口を使わなかった。同時に、在庫が「入れるのは可だが headline にしない」条件付きで許容していた
  Route A (`natLen (modelCode S)` 版の弱い two-part bound) も**採らなかった** (K(S) 版 (B) が入ったため不要)。
  slug は他文書参照のため register に残す。

**判定 (現時点)**: R-W2a 回避済 / R-W2b 未発動 / R-W2c 未発動、**さらに §Phase P10 の「本 Phase 全体が撤退候補」も
未発動** (P10 は proof-done で着地)。⟹ **第 2 波で発動した撤退ラインは 0 件**。子 plan
(Ω 非計算性、R-ONC0–3) でも発動 0 ⟹ **第 2 波 + 後継 scope を通じて撤退ライン発動は 0 件**。残る撤退ラインは無く、
残 scope (加法版 Levin) は撤退ではなく別 object の新規建て (§ゴール / Scope の達成判定)。

---

## residual slug 方針

inventory 推奨に従い **第 1 波 §Out の単一 `wall:prefix-free-tower` は撤回** (over-estimation、Kraft 既存)。
第 2 波の途中 sorry は **object 別の `plan:` slug** に分割し、各 slug は将来分割する子 plan の filename stem
(kebab-case、`-plan.md` を除く) と一致させる:

| slug (`@residual(plan:…)`) | 状態 | object |
|---|---|---|
| `kolmogorov-w2-prefix-machine` | 退避不要で closure (子 plan 起票せず) | Gateway atom (U_pf / PrefixFree / K) |
| `kolmogorov-w2-universal-prob` | 同上 | P7 P_U 定義 + 下界 |
| `kolmogorov-w2-omega` | 同上 | P9 Ω 収束 |
| `kolmogorov-w2-kss` | **同上 (P10 着地で closure)** — crux まで含めて退避せず着地したため子 plan 起票は不要 | P10 十分統計量 |
| `kolmogorov-w2-omega-noncomputable` | **closure (2026-07-25)** — 子 plan [`kolmogorov-w2-omega-noncomputable-plan.md`](kolmogorov-w2-omega-noncomputable-plan.md) が N0–N5 全段 proof-done、撤退ライン発動 0 ⟹ 本 slug の `sorry` は 0 本 | **Ω 自体の非計算性** (`IsComputableENNReal` の自前定義 + Chaitin 論法 → §Phase P9) |
| `kolmogorov-w2-levin` | **唯一の残 scope (子 plan 未作成)、コード側 `sorry` は 0 本** | **加法版 Levin 定理** (下記) |

**新 slug `kolmogorov-w2-machine-partrec` は追加しない**: P10 在庫 §壁の列挙が crux
(`payloadComplexity_two_part_le`) 用の共有 sorry 補題 slug として推奨していたが、**crux が退避なしで closure した
ため貼る先の `sorry` が存在しない**。「`sorry` の無い slug は登録しない」(register の divergence 防止) ⟹ 不採用。
在庫だけを読むと未登録が抜けに見えるのでここに記録を残す。

`kolmogorov-w2-omega-noncomputable` を **`wall:` ではなく `plan:`** としたのは、実数計算可能性が Mathlib に無いのが
「解析が難しい (hard)」ではなく「定式化と自作インフラを選ぶ (big)」側だからである。**この分類は closure で実測
追認された** (`wall:` を貼らずに proof-done、子 §Settled facts)。

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

- **claim (confidence = `loogle-neg`)**: **Mathlib に「計算可能実数 / 計算可能解析」の資産は無い**
  (`Computable, Real` → Found 0 / `ComputableReal` → unknown identifier)。**claim は closure 後も不変**で、
  Ω 非計算性は述語 `IsComputableENNReal` の自前定義で述べた。
  - ⚠️ **混同注意 (子 §Settled facts が SoT)**: 「標準の計算可能実数述語を Lean で**述べる**」ことは可能
    (`Denumerable ℚ` → `Primcodable ℚ`、machine 確認済)。塞がっているのは**その述語からの含意を証明する**側で、
    丸めに ℚ 上の計算可能除算が要る (`Primrec, Rat` / `Primrec, Int` とも Found 0)。子 plan が一度この 2 つを
    混同した誤記を持っていたので、confidence を分けて参照すること。

- **claim (confidence = `loogle-neg`、verbatim 出力の SoT は P10 在庫 §G / §壁の列挙)**: §14.12 の全 object
  (`SufficientStatistic` / `structureFunction` / `MinimumDescriptionLength` / `descriptionLength` /
  `KolmogorovComplexity`) と `Primcodable (Finset _)` / `Primcodable (Multiset _)` / `Primrec` × `encodeNat` は
  **Mathlib に Found 0**。いずれも壁ではなく (a) 定義の選択 / (b) 設計での回避 / (c) 自作で処理済 (P10 で実測裏付け)。

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
  **prefix K の**非計算性)
- `Levin.lean` — P8 (`payloadComplexity` / `padDelimit` + factor-2 関係の flagship)
- `SufficientStatistic.lean` — P10 (KSS / MDL。定義群 + 構造関数 + **bit codec の `Primrec` 化 +
  自己シミュレーション crux**。`payloadDispatch_primrec` は後継 scope が消費するため Primrec 版が本体)
- `PrefixComputability.lean` — 機械の partrec 性 + 停止集合の決定不能性 (Ω 非計算性の前哨 gateway atom)
- `OmegaNoncomputable.lean` — **Ω 自体の非計算性** (`IsComputableENNReal` / 有界機械 `prefixEvaln` / 下からの
  近似列 + 探索 + headline。子 plan が SoT)

各ファイル追加時に `InformationTheory.lean` へ import 行を登録。`private` helper を共有する sub-module は
同一ファイルに置く (file-scoped `private`)。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正時。決着済 entry は削除 (git が履歴)、active な判断のみ残す。

(#1 = 単一壁 slug の撤回は gateway atom / P7 / P9 の通過で決着 ⟹ §settled facts に集約。#3 = P8 を crux として
保守的に扱う判断、#5 = P8 着手ゲート (strength diff) はいずれも P8 の着地で決着 ⟹ §Phase P8 / §settled facts /
§Approach「under-estimation ガード」に集約。**#4 = Ω 非計算性の park / 順序を後ろへ、の判断は子 plan の closure で
決着** ⟹ §Phase P9 + §residual slug 方針に集約。いずれも判断ログからは畳んだ。番号は他文書参照を壊さないため
振り直さない。)

2. **U_pf は第 1 波 `universalEval` の拡張でなく別機械 (active、inventory 採用)**: literal `false::bs` が前置閉で
   prefix-free でないため。再利用は interpret 委譲機構のみ。§定義形の設計判断。
6. **P8 は factor-2 形で着地、加法版は plan 段のみで park (active、strength diff ゲートの決着)**: 着手前ゲートの
   3 択は (i) **原理的に不可能** (`K = 2·m + 1` が恒等式) / (ii) 加法的普遍機械の構成 = 別 moonshot 級の後継ルート /
   (iii) 採用のうえ「言い換え」から「証明」へ格上げ、で決着した (§Phase P8)。flagship は
   `prefixComplexity_le_two_mul_neg_logb_universalProb` + P7 下界 = 両側 factor-2 で、§ゴールの目標地点も訂正済
   (当初の加法版の野心は削除せず後継ルートへ移した)。**加法版はコード側に `sorry` を置かない** — この機械では
   真偽不明であり、偽かもしれない命題に `@residual` を貼るのは defect ⟹ park は plan 段のみ、決着条件は
   §settled facts の human-judgment entry が持つ。factor-2 版を教科書 Levin と称するのは恒久的に禁止。
7. **P10 は crux まで proof-done、新 slug は建てない (active、在庫推奨からの逸脱を明示)**: P10 在庫は crux
   `payloadComplexity_two_part_le` を共有 sorry 補題にする前提で新 slug `kolmogorov-w2-machine-partrec` を
   推奨していたが、bit codec の `Primrec` 化 + `Nat.Partrec.Code.eval_part` による自己シミュレーションが実際に
   組めたため **crux ごと closure** ⟹ 貼る先の `sorry` が存在せず slug を登録しない (§residual slug 方針)。
   同時に在庫提案の撤退ライン R-W2c も未発動、Route A (退化する弱い版) も採らなかった。**P10 の係数 4 を
   `twoPartLength` の定義側に埋め込む判断は維持** — 教科書形の係数 1 はこの機械では偽であり、定義に埋めるのが
   唯一の honest な回避 (name laundering 禁止、§Phase P10)。

# Ch.14 Kolmogorov 複雑性 — 山場探求 (scouting)

> **Status**: SCOUTING (2026-07-20)。relay セッション前の地図。まだ plan でも inventory でもない。
> **Goal**: Cover & Thomas 2nd ed. Ch.14 のどの定理が「章の山場 (headline)」になるかを、
> Mathlib computability 資産に照らして仕分ける。SoT は着手確定後の
> `kolmogorov-moonshot-plan.md` + `kolmogorov-mathlib-inventory.md`(未作成)。
> **注意**: CT の節番号は記憶ベース。原典 PDF が repo に無いので、着手前に本文と照合すること
> (数学的 statement 自体は標準形で確度高、番号のみ要 verbatim 確認)。

## 0. 章全体を貫く最重要の分岐 — plain C vs prefix K

Ch.14 は 2 つの複雑性を混在させて書かれている:

- **plain 複雑性 C(x)**(素朴、万能機械 U 上の最短プログラム長)
- **prefix 複雑性 K(x)**(自己限定=prefix-free 機械上。普遍確率と Kraft 不等式が成立する版)

**Mathlib の現状**:
- 万能機械(`Nat.Partrec.Code` + `eval`/`evaln`)、停止問題、Gödel 数、符号化 = **すべて在る**。
  → **plain C の背骨は既存資産で建つ**。
- **prefix-free 機械 / 自己限定符号 / Kraft on programs = 完全に不在**。
  → **普遍確率 P_U・符号化定理・Ω の塔は、まず prefix-free 機械インフラを自作**してから。
  これが本章唯一の genuine「解析/量の壁」。

⟹ **relay の第一目標は plain C の背骨に絞るのが正着**。4 本の headline(不変性・数え上げ・
K↔H・非計算可能性)がすべて plain C だけで閉じ、しかも既存の entropy/AEP 資産と噛み合う。
prefix 塔は別 moonshot(第 2 波)に隔離する。

## 1. 山場マップ(CT Ch.14 の peaks)

| # | 定理 (CT 2nd ed, 番号=要確認) | 一言 statement | 複雑性種別 | 実現可能性 | 主要 Mathlib 資産 / gap |
|---|---|---|---|---|---|
| **P1** | **不変性定理** (Thm 14.2.1) | 万能 U に対し任意の機械 A で `C_U(x) ≤ C_A(x) + c_A` | plain | ★ 高(gateway) | `exists_code` + `smn`/合成。純粋に万能性。**背骨の礎石** |
| **P2** | 上界 (Thm 14.2.2/14.2.3) | `C(x) ≤ l(x) + c`、条件版 `C(x|l(x)) ≤ l(x)+c`、自己限定長で `+2log l(x)` | plain | ★ 高 | `Code.const` で恒等プログラム。初等 |
| **P3** | **数え上げ + 非圧縮存在** (Thm 14.2.4) | `#{x : C(x) < k} < 2^k` ⟹ ほとんどの文字列は非圧縮 | plain | ★ 高(iconic・小) | プログラム長 < k は 2^k 未満。`Finset.card` + `Nat.size`。純カウント |
| **P4** | **K↔エントロピー** (Thm 14.3.1) | i.i.d. で `(1/n) E[C(X^n\|n)] → H(X)` | plain | ◎ 中(**flagship**) | 既存 entropy/AEP/typical set 資産と合流。**本章の真の山場** |
| **P5** | **非計算可能性** (Thm 14.8) | `C` は計算可能関数でない(Berry/停止経由) | plain | ★ 中〜高 | `halting_problem` / `rice` が背骨。iconic |
| **P6** | 非圧縮列の SLLN (Thm 14.5.1) | `C(x_1..x_n\|n) ≥ n` なら 1 の頻度 → 1/2 | plain | ○ 中 | 数え上げ + 既存確率補題。美しいが中量 |
| **P7** | 普遍確率下界 (Thm 14.6.1) | `P_U(x) ≥ c·2^{-K(x)}`(片側) | prefix | △ 中〜大 | **prefix-free 機械が要**。gap |
| **P8** | **符号化定理** (Levin, Thm 14.x) | `-log P_U(x) = K(x) + O(1)`(等号) | prefix | ✖ 大(深い) | prefix 塔の頂点。等号方向が難 |
| **P9** | **Chaitin の Ω** (§14.9) | `Ω` = 万能停止確率、非計算的・アルゴリズム的ランダム | prefix | ✖ 大 | Ω の well-defined 性に prefix-free 収束が必須 |
| **P10** | Kolmogorov 十分統計量 (§14.12) | KSS / MDL 原理 | 混在 | ✖ 大(先送り) | 上位塔の後 |

★=既存資産で直行 / ◎=既存 IT 資産と合流する flagship / ○=中量自作 / △=prefix 前提 / ✖=prefix 塔 or 深い

## 2. 推奨 relay アーク — plain C の背骨(DAG)

```
        P1 不変性定理 (gateway atom)
          │  ← C(x) が well-defined (const で非空 ⟹ Nat.sInf 到達) を含む
          ▼
   ┌──── P2 上界 ────┐
   │                 │
   ▼                 ▼
P3 数え上げ        (P2 条件上界)
 非圧縮存在           │
   │                 ▼
   │         ┌─── P4 K↔H (flagship @[entry_point]) ───┐
   │         │   上界 = P2 条件上界 + typical set 符号化   │
   │         │   下界 = P3 数え上げ + AEP                 │
   ▼         ▼                                          │
P6 非圧縮 SLLN   P5 非計算可能性 (halting_problem)         │
 (stretch)      (独立 iconic、P1/P3 のみ依存)              │
```

- **gateway atom = 長さ加法 U の構成 + P1 不変性 + P2 literal 上界**(3 点セット、§4 参照)。
  これを 1 本 `lean-implementer` に投げ、(i) naive Gödel 数ルートが加法定数を出せないことを最初に確認、
  (ii) literal/interpret 2 モードの U を建て、(iii) `C_U ≤ C_A + c_A`(P1)と `C(x) ≤ l(x)+O(1)`(P2)を通す。
  **U 構成が make-or-break**——ここが通れば背骨の残り(P3-P5)は既存資産で直線的。詰まれば定義形を再設計。
- **flagship = P4 (K↔H)**。この project が Ch.14 を持つ意味そのもの(計算量↔情報量)。
  headline `@[entry_point]`。上界・下界とも既存 entropy/typical-set 資産に接続する点が最大の勝ち筋。
- **P5 非計算可能性**は P4 と独立に走れる(P1/P3 のみ依存)ので relay の並走レーン候補。

## 3. Mathlib 資産台帳(背骨に効くもの、verbatim)

**万能機械 — `Mathlib/Computability/PartrecCode.lean`**
- `Nat.Partrec.Code` : プログラムの inductive。`eval : Code → ℕ →. ℕ`(万能解釈器)。
- `evaln : ℕ → Code → ℕ → Option ℕ`(有界・**計算可能**)= 数え上げ/停止の要。
- `exists_code : Nat.Partrec f ↔ ∃ c, eval c = f`(不変性の核)。
- `smn`(S-m-n)、`fixed_point`/`fixed_point₂`(再帰定理)。
- `encodeCode : Code → ℕ` / `ofNatCode : ℕ → Code`(計算可能 Gödel 数、`Code ≃ ℕ`)。

**非計算可能性 — `Mathlib/Computability/Halting.lean`**
- `ComputablePred.halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom`
- `halting_problem_re` / `halting_problem_not_re`、`rice` / `rice₂`(Rice の定理)。

**符号化 — `Mathlib/Computability/Encoding.lean`**
- `Encoding`/`FinEncoding`、`List α`/`Bool`/`ℕ`/pair の符号化、ℕ の 2 進符号。

**gap(この project で自作)**: Kolmogorov 複雑性の定義そのもの / prefix-free 機械 / program 上の Kraft。

## 4. 定義形(Mathlib-shape-driven)— ⚠️ naive 形は却下、長さ加法 U へ pivot

### ❌ 却下された naive 形(2026-07-20 inventory + 実体照合で棄却)

当初案 `C(x) := sInf { Nat.size p | x ∈ eval (ofNat Code p) 0 }`(プログラム = Gödel 数 `p`、
長さ = `Nat.size(encodeCode c)`)は **P2 上界すら成立せず P4 flagship を破壊する**。理由(Mathlib
`PartrecCode.lean` の def から機械確認、settled fact):

- `Code.const (n+1) = comp succ (Code.const n)`(:98、unary の反復合成)。
- `encodeCode (comp cf cg) = 2*(2*Nat.pair(encodeCode cf)(encodeCode cg)+1)+4`(:14)、`Nat.pair` は二次。
- ⟹ `e_n := encodeCode(const n)` は `e_{n+1} ≈ 4·e_n²`(**二重指数**)⟹ `Nat.size(encodeCode(const x)) ≈ 2^x`。
- ⟹ `x` を出力する最短プログラムのコストが `≈ 2^x` bit。**`C(x) ≤ l(x)+c`(P2)が偽**、
  `(1/n)E[C(X^n|n)]` は `H` でなく**定数倍**に化け **P4 が崩れる**。
- AST ノード数を長さに採る逃げ道も封じられる: `const x` が unary ゆえノード数 O(x)(literal `x` の
  bit 長 log x より指数的に大)。**Gödel 数でも AST でも加法定数は原理的に出ない。**

これは **Mathlib 壁ではなく定義形の選択問題**(loogle 0-hit ではなく、間違った長さ尺度を選んだこと)。

### ✅ 採る形 — bit 列を読む長さ加法な専用万能機械 U

- **プログラム = bit 列**(`ℕ` を `Nat.size` bit で読むか `List Bool`)。長さ `l(p) := Nat.size p`。
- **専用 U を自作**(gap #1、make-or-break、~100-300 行):
  - **literal モード**: `U (0 ∷ x_bits) = x` を持たせる ⟹ `C(x) ≤ l(x) + O(1)`(P2 が回復)。
  - **interpret モード**: `U (1 ∷ selfDelim(idx) ∷ input) = eval (ofNat Code idx) input`。
    `selfDelim` は idx を自己限定符号化(この符号化は prefix-free 塔とは無関係、単に idx を可逆に埋める)。
- `C(x) := sInf { Nat.size p | U p = x }`。非空性は literal モードから ⟹ `Nat.sInf` が到達最小値
  (定義本体に `sorry` 不要)。条件版 `C(x|y) := sInf { Nat.size p | U (encode y ∷ p) = x }` を primary に。
- **不変性 P1**: 別機械 A = 部分再帰 `ℕ →. ℕ` は `exists_code` で `eval c_A` に落ち、interpret モードの
  固定 selector `1 ∷ selfDelim(c_A の idx)` を前置 ⟹ `C_U(x) ≤ C_A(x) + c_A`。加法定数 = selector 長。

**設計上の効用**: literal モードが P2 を、interpret モードが P1 不変性を、両モード非空性が well-defined 性を
それぞれ担保。`Nat.size` を長さに採ることで数え上げ P3 は `Nat` 初等補題で閉じる。**U の構成が本章の crux**。

## 5. 着手前に潰す modeling 論点

1. **入力なし版 `eval c 0` vs 条件版 `eval c y`**: CT は条件複雑性を多用(特に P4 の `C(X^n|n)`)。
   最初から条件版 `C(x|y)` を primary に定義し、無条件は `C(x) := C(x|0)` の特殊化にすると P4 が楽。
2. **長さの取り方**: `Nat.size`(ビット長)で統一。自己限定 `+2 log l` は P2/P4 でのみ要る。
3. **不変性の「別機械 A」の定式化**: A を「部分再帰な解釈器 `ℕ →. ℕ`」として取り、`exists_code`
   で `eval c_A` に落とす。ここが P1 の全て。gateway atom で機構を確定させる。
4. **prefix 塔は触らない**(第 2 波に隔離)。P7-P9 は本 relay の scope 外と明記。

## 6. relay スコープ提案(第 1 波)

**In(背骨、plain C)**: P1 不変性 → P2 上界 → P3 数え上げ/非圧縮 → **P4 K↔H(flagship)** → P5 非計算可能性。
余力で P6 SLLN。**headline 4-5 本、すべて既存 Mathlib 万能機械 + entropy/AEP 資産で閉じる見込み**。

**Out(第 2 波 = 別 moonshot)**: prefix-free 機械インフラ自作 → P7 普遍確率 → P8 符号化定理 → P9 Ω。
ここが唯一の genuine 壁(未整備インフラ)で、切り分けておく。

**次の一手**: (a) ✅ `mathlib-inventory` 完了(`kolmogorov-mathlib-inventory.md`、318 行)。
(b) `lean-planner` で `kolmogorov-moonshot-plan.md` を起こす(crux = 長さ加法 U 構成、§4 の訂正形が SoT)。
(c) gateway atom(U 構成 + P1 + P2 literal)を 1 本 dispatch して make-or-break を確認。

# Ch.14 第 2 波 Phase P10 (Kolmogorov 十分統計量, CT §14.12) Mathlib/in-tree API 在庫

> **親計画**: [`kolmogorov-w2-moonshot-plan.md`](kolmogorov-w2-moonshot-plan.md) §Phase P10 / §residual slug 方針
> (park slug `plan:kolmogorov-w2-kss`)。既存の family 在庫 = [`kolmogorov-w2-inventory.md`](kolmogorov-w2-inventory.md)
> (本ファイルは §自作 5「P10 十分統計量」を実装可能粒度まで掘ったもの)。
> **調査日 2026-07-25 / 対象機械 = `prefixUniversalEval` (`PrefixMachine.lean:172`)。**

## 一行サマリ

**P10 の plumbing で使う Mathlib API はほぼ 100% 既存** (`Nat.log`/`Nat.clog`/`Nat.pair` の値評価・`Primrec` 閉包・
`Nat.Partrec.Code.eval_part`/`exists_code` は全部ある)。**自作は「定義群 6 本 + `natLen` 補題 2 本 + crux 1 本」**で、
うち **crux 以外は本調査で machine 検証済み** (使い捨て probe を `lake env lean` に通した実測: §着手 skeleton の
定義 6 + 定理 7 が 0 error / 0 sorry、two-part decoder の `Computable` 証明も 8 行で通った)。**残る crux は 1 本だけ**: 機械の自己シミュレーション
(`payloadComplexity_two_part_le`) = 教科書形 `K(x) ≤ K(S) + log|S| + c` の **K(S) 側**を出すための唯一の穴。
**`wall:` は打たない** (Mathlib 不在の解析ではなく bit codec の `Primrec` 化という選択 = big)。

**汚染 (factor 2) の会計 — 結論**: 第 2 波の 2 倍係数は **先頭項 K(S) には掛からない**。
payload 世界 (`payloadComplexity`) で述べれば加法的で、`K = 2·m + 1` で変換するとき 2 倍が掛かるのは
**(a) index 項 (2·⌈log₂|S|⌉ → 4·⌈log₂|S|⌉) と (b) 加法定数 (c → 2c) だけ**。K(S) の係数はちょうど 1
(両辺が同じ `2·(payload)+1` を通るので相殺する)。⟹ **定義側に `4 *` を明示的に埋め込めば、以降すべて
「加法定数のみの汚染」に落ちる** (bridge 補題不要)。

---

## P10 の到達形 (推奨、親計画 §Phase P10 の成果物欄を実装可能形に具体化)

```lean
-- headline 1: two-part 符号の達成可能性 (CT §14.12 の K(x) ≤ K(S) + log|S| + c に対応)
@[entry_point] theorem prefixComplexity_le_twoPartLength :
    ∃ c : ℕ, ∀ (x : ℕ) (S : Finset ℕ), x ∈ S → prefixComplexity x ≤ twoPartLength S + c

-- headline 2: MDL 原理 (両側、|K(x) − mdl(x)| ≤ c)
@[entry_point] theorem mdlComplexity_sub_prefixComplexity_le :
    ∃ c : ℕ, ∀ x : ℕ, mdlComplexity x ≤ prefixComplexity x + c
                        ∧ prefixComplexity x ≤ mdlComplexity x + c
```

証明戦略 (pseudo-Lean、payload 世界で組んで最後に K へ 1 回変換する):

```
-- crux (共有 sorry 候補、self-simulation): payload を渡すと加法的
payloadComplexity_two_part_le A hA :  ∃ c, ∀ x y i, x ∈ A y i →
    payloadComplexity x ≤ payloadComplexity y + 2 * natLen i + c
  ⇐ pack := selfDelimit (encodeNat i) ++ d_y ++ [true]           -- index を自己限定、payload は末尾
    N := decodeNat pack,  |encodeNat N| = |pack| = 2·natLen i + m(y) + 2
    program := selfDelimit (true :: replicate idx true ++ false :: encodeNat N)
    code は pack を parse して `decodePayload d_y` を走らせ A を適用   -- ここが self-simulation
-- K への変換 (`prefixComplexity_eq_two_mul_payloadComplexity_add_one`, Levin.lean:114)
K(x) = 2·m(x)+1 ≤ 2·(m(y) + 2·natLen i + c) + 1 = K(y) + 4·natLen i + 2c
-- 具体化: y := modelCode S, i := S.sort の x の位置, A := 「list を decode して i 番目」
natLen i ≤ Nat.clog 2 S.card                                       -- 検証済 1 行
⟹ K(x) ≤ modelComplexity S + 4 * Nat.clog 2 S.card + c'  =  twoPartLength S + c'
-- MDL 上側は singleton モデルで: mdl x ≤ twoPartLength {x} = modelComplexity {x} (clog 2 1 = 0)
   ≤ K(x) + c''                                                    -- crux の i = 0 特殊化 (natLen 0 = 0)
```

---

## API 在庫テーブル

### A. モデル (有限集合) の符号化

| 概念 | Mathlib API (署名 verbatim) | file:line | 状態 | P10 での扱い |
|---|---|---|---|---|
| `Finset` の Encodable | `instance Finset.encodable [Encodable α] : Encodable (Finset α)` | `Mathlib/Logic/Equiv/Finset.lean:22` | ✅ 既存 (`Multiset` 経由) | **使わない** (下記 §Key-preconditions ①) |
| `Finset` の Denumerable | `instance finset : Denumerable (Finset α)` (`variable [Denumerable α]`) | `Mathlib/Logic/Equiv/Finset.lean:109` | ✅ 既存 (`Finset.encodable` と**別符号**) | 使わない |
| `List` の Encodable | `instance _root_.List.encodable : Encodable (List α)` | `Mathlib/Logic/Equiv/List.lean:63` | ✅ 既存 | **採用** (`modelCode` の土台) |
| 符号本体 | `def encodeList : List α → ℕ \| [] => 0 \| a :: l => succ (pair (encode a) (encodeList l))` | `Mathlib/Logic/Equiv/List.lean:44` | ✅ 既存 | サイズ挙動の根拠 (下記) |
| 復号本体 | `def decodeList : ℕ → Option (List α)` (`0 => some []`, `succ v => (·::·) <$> decode v₁ <*> decodeList v₂`) | `Mathlib/Logic/Equiv/List.lean:49` | ✅ 既存 | decoder が使う |
| round-trip | `class Encodable` の field `encodek : ∀ a, decode (encode a) = some a` (`attribute [simp]` 済) | `Mathlib/Logic/Encodable/Basic.lean:58` (simp 属性 `:60`) | ✅ 既存 | decoder 正当性 |
| **符号長の上界補題** | — | — | ❌ **不在** | **`encode` のサイズ補題は Mathlib に 1 本も無い**。P10 は「サイズを使わない設計」で回避 (§推奨定義形) |

**符号長の実測 (machine 検証、`#eval`)**: `natLen (encode l)` は **`|l|` に対して指数的**に増える
(`encodeList` が cons ごとに `Nat.pair` = 二乗を掛けるため) —
`[1,2,3]` → **15** bit (`encode = 29586`) / `[1..6]` → **174** / `[1..10]` → **3480** / `[1..12]` → **14941**
(比較: `[1000000]` は 40)。

⟹ **`natLen (modelCode S)` を「モデルの記述長」として使う定式化は真だが退化**する (12 要素モデルで 14941 bit =
literal 上界 `K(x) ≤ 2·natLen x + 3` より常に悪い)。**モデル項は必ず `prefixComplexity (modelCode S)` (= K(S)) で
書く**こと (K は最短記述長なので符号の冗長さに影響されない)。§Honest scope call の (C4)。
なお `Encodable.encode ({9,5,2} : Finset ℕ) = Encodable.encode ([2,5,9] : List ℕ) = 68674372` (machine 実測) で
両符号は数値一致するが、**橋渡し補題は Mathlib に無い**ので `modelCode` は最初から sorted list で定義する。

### B. 有限集合の中の元を index で指す

| 概念 | Mathlib API (署名 verbatim) | file:line | 状態 | P10 での扱い |
|---|---|---|---|---|
| ソート済リスト | `def sort (s : Finset α) (r : α → α → Prop := by exact fun a b => a ≤ b) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r] : List α` | `Mathlib/Data/Finset/Sort.lean:33` | ✅ 既存 | **採用**。`α = ℕ`, `r = (· ≤ ·)` で 4 つの instance は自動充足 (machine 確認) |
| 元の一致 | `theorem mem_sort {a : α} : a ∈ sort s r ↔ a ∈ s` | `:109` | ✅ | `x ∈ S` ↔ list membership |
| 長さ | `theorem length_sort : (sort s r).length = s.card` | `:113` | ✅ | index 範囲 = `S.card` |
| 重複なし | `theorem sort_nodup : (sort s r).Nodup` | `:56` | ✅ | index の一意性 (使うなら) |
| 単調 index | `def orderIsoOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ≃o s` / `def orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ↪o α` / 実体 `theorem orderEmbOfFin_apply … (i : Fin k) : s.orderEmbOfFin h i = s.sort[i]'(by rw [length_sort, h]; exact i.2)` (`rfl`) / `orderIsoOfFin_symm_apply … : ↑((s.orderIsoOfFin h).symm x) = s.sort.idxOf ↑x` | `:190` / `:198` / `:210` / `:206` | ✅ 既存 | **使わない** — `Fin k` + `h : card = k` の cast が decoder 側で邪魔で、しかも実体 (`:210`, `rfl`) が list index そのものなので直接 list を使う |
| index → 元 (Prop) | `theorem getElem_of_mem : ∀ {a} {l : List α}, a ∈ l → ∃ (i : Nat) (h : i < l.length), l[i]'h = a` | `Init/Data/List/Lemmas.lean:467` | ✅ | **採用** (`exists_index_of_mem` に使用、machine 検証済) |
| 元 → index | `theorem idxOf_lt_length_of_mem [BEq α] [EquivBEq α] {l : List α} (h : a ∈ l) : l.idxOf a < l.length` | `Init/Data/List/Find.lean:1164` | ✅ | 計算的に index が要るとき (`Fin`/逆写像を作るなら) |
| ↑と getElem | `theorem getElem?_idxOf [BEq α] [LawfulBEq α] {a : α} {l : List α} (h : a ∈ l) : l[idxOf a l]? = some a` | `Mathlib/Data/List/Basic.lean:652` | ✅ | 同上 (引数順が core と揺れているので使用時に verbatim 再確認) |
| `Finset.equivFin` | `Finset.equivFin` | `Mathlib/Data/Fintype/EquivFin.lean` | ✅ 既存 | 使わない (順序を保証しない) |

### C. bit 長算術 (`Nat.log 2` / `Nat.clog 2` / in-tree `natLen`)

| 概念 | API (署名 verbatim) | file:line | 状態 | P10 での扱い |
|---|---|---|---|---|
| ⌈log₂⌉ | `theorem le_pow_clog {b : ℕ} (hb : 1 < b) (x : ℕ) : x ≤ b ^ clog b x` | `Mathlib/Data/Nat/Log.lean:441` | ✅ | **index 幅の主役** (`i < card ≤ 2^clog card`) |
| Galois | `theorem clog_le_iff_le_pow {b : ℕ} (hb : 1 < b) {x y : ℕ} : clog b x ≤ y ↔ x ≤ b ^ y` | `:387` | ✅ | clog の上下変換 |
| 弱版 | `theorem clog_le_of_le_pow {b x y : ℕ} (h : x ≤ b ^ y) : clog b x ≤ y` (`1 < b` 不要) | `:421` | ✅ | 同上 |
| 単調 | `theorem clog_mono_right (b : ℕ) {n m : ℕ} (h : n ≤ m) : clog b n ≤ clog b m` | `:445` | ✅ | **brief の `Nat.clog_le_clog_of_le` は存在しない**。正しい名前はこれ |
| 境界 | `theorem clog_of_right_le_one {n : ℕ} (hn : n ≤ 1) (b : ℕ) : clog b n = 0` / `@[simp] clog_zero_right`, `@[simp] clog_one_right` | `:352` / `:357`, `:364` | ✅ | **`clog 2 0 = 0` と `clog 2 1 = 0`** (machine 実測: 0, 0, `clog 2 2 = 1`, `clog 2 3 = 2`) |
| 正値 | `theorem clog_pos {b n : ℕ} (hb : 1 < b) (hn : 1 < n) : 0 < clog b n` | `:400` | ✅ | 非退化 (2 元以上のモデルは index bit を要する) |
| べき | `@[simp] theorem clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x` | `:433` | ✅ | `clog 2 1024 = 10` (実測) |
| 下 vs 上 | `@[simp] theorem log_le_clog (b n : ℕ) : log b n ≤ clog b n` | `:469` | ✅ | log/clog 比較 |
| ⌊log₂⌋ | `pow_log_le_self (b : ℕ) {x : ℕ} (hx : x ≠ 0) : b ^ log b x ≤ x` / `lt_pow_succ_log_self {b : ℕ} (hb : 1 < b) (x : ℕ) : x < b ^ (log b x).succ` | `:171` / `:196` | ✅ | 実 log との比較で使うなら |
| log 境界/単調 | `@[simp] log_zero_right (b) : log b 0 = 0` / `@[simp] log_one_right (b) : log b 1 = 0` / `@[mono, gcongr] log_mono_right {b n m} (h : n ≤ m) : log b n ≤ log b m` | `:145` / `:153` / `:247` | ✅ | 実測 `log 2 0 = 0`, `log 2 1 = 0` |
| **実 log への橋** | `theorem natCeil_logb_natCast (b : ℕ) (n : ℕ) : ⌈logb b n⌉₊ = Nat.clog b n` (同 floor 版 `natFloor_logb_natCast … = Nat.log b n` `:400`、`lemma natLog_le_logb (a b : ℕ) : Nat.log b a ≤ Real.logb b a` `:421`) | `Mathlib/Analysis/SpecialFunctions/Log/Base.lean:411` | ✅ **既存** | **`Nat.clog 2 \|S\|` が教科書の `⌈log₂\|S\|⌉` そのものである verbatim 根拠**。実数形が要求されたらここを通す |
| in-tree bit 長 | `def natLen (x : ℕ) : ℕ := (encodeNat x).length` | `InformationTheory/Shannon/Kolmogorov/UniversalMachine.lean:62` | ✅ 既存 | **`(Computability.encodeNat n).length = natLen n` は `rfl`** (定義そのもの。`EntropyRate.lean:442` が `show … from rfl` で実使用) |
| natLen 上界 | `theorem natLen_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ natLen n ≤ 2 * n` | `:84` | ✅ | 実 log との比較 (`Incompressible.lean:102` の雛形) |
| natLen 逆向き | `theorem natLen_le_of_lt_two_pow (x k : ℕ) (h : x < 2 ^ k) : natLen x ≤ k` | `:89` | ✅ | **index 幅の主役**。`clog` と組んで 1 行 |
| **natLen 下界** | — | — | ❌ **不在** | `n < 2 ^ natLen n` が無い ⟹ **natLen の単調性も無い**。自作 (§自作 2) |

**machine 実測 (verbatim)**: `natLen 0 = 0`, `natLen 1 = 1`, `natLen 2 = 2`, `natLen 5 = 3`, `natLen 1000 = 10`,
`Nat.log 2 1000 = 9`, `Nat.log 2 4 = 2`, `natLen 4 = 3` ⟹ `natLen n = Nat.log 2 n + 1` (n ≥ 1)、`natLen 0 = 0`。

### D. pairing のコスト

| 概念 | API (署名 verbatim) | file:line | 状態 | P10 での扱い |
|---|---|---|---|---|
| pair | `def pair (a b : ℕ) : ℕ := if a < b then b * b + a else a * a + a + b` | `Mathlib/Data/Nat/Pairing.lean:38` | ✅ | 2 引数を 1 個の ℕ に |
| unpair | `def unpair (n : ℕ) : ℕ × ℕ` / `theorem unpair_pair (a b : ℕ) : unpair (pair a b) = (a, b)` | `:43` / `:61` | ✅ | decoder 側 |
| **値の上界** | `theorem pair_lt_max_add_one_sq (m n : ℕ) : pair m n < (max m n + 1) ^ 2` | `:136` | ✅ **既存** | **pairing コストの唯一の必要補題**。`natLen_le_of_lt_two_pow` と組んで `natLen (pair a b) ≤ 2 * natLen (max a b)` |
| 値の下界 | `theorem max_sq_add_min_le_pair (m n : ℕ) : max m n ^ 2 + min m n ≤ pair m n` | `:140` | ✅ | 「pairing は本当に 2 倍かかる」= 回避不能の根拠 |
| その他 | `add_le_pair (m n) : m + n ≤ pair m n` / `left_le_pair` / `right_le_pair` / `pair_lt_pair_left` / `pair_lt_pair_right` | `:148` / `:102` / `:104` / `:112` / `:126` | ✅ | 単調性 |

**machine 実測**: `natLen 1000 = 10`, `natLen 5 = 3`, **`natLen (Nat.pair 1000 5) = 20`**, `natLen (Nat.pair 5 1000) = 20`
⟹ **`Nat.pair` は「大きい方の bit 長をちょうど 2 倍」にする** (和ではなく max の 2 倍)。
⟹ 機械の `2 * q.length` と重なって **`Nat.pair` 経路の two-part 符号は `4 * max(...)`** になる。
**bit level の代替**: `selfDelimit` (`PrefixMachine.lean:107`, prefix-free 既証明) で連結すると加法
(`2·natLen i + m + 2`) になるが、`decodeNat (bs ++ cs)` / `natLen (decodeNat …)` を部品に関係づける補題は
**Mathlib にも in-tree にも 0 本** (`Computability.encodeNat` に付く補題は Mathlib 全体で
`Computability.decode_encodeNat` の **1 本だけ** = loogle 実測)。⟹ §自作 3。

### E. decoder を `Nat.Partrec.Code` に載せる (P10 で唯一「難しそう」に見えた部分 → **8 行で通った**)

| 概念 | API (署名 verbatim) | file:line | 状態 |
|---|---|---|---|
| code の存在 | `theorem exists_code {f : ℕ →. ℕ} : Nat.Partrec f ↔ ∃ c : Code, eval c = f` | `Mathlib/Computability/PartrecCode.lean:533` | ✅ (in-tree `prefix_invariance` が内部で使用) |
| **eval の partrec 性** | `theorem eval_part : Partrec₂ eval` | `:994` | ✅ **既存** ← **self-simulation の中核が Mathlib にある** |
| decode/encode の primrec | `protected theorem decode : Primrec (@decode α _)` / `protected theorem encode : Primrec (@encode α _)` (両方 `[Primcodable α]`) | `Mathlib/Computability/Primrec/Basic.lean:187` / `:184` | ✅ |
| list の Primcodable | `instance list : Primcodable (List α)` | `Mathlib/Computability/Primrec/List.lean:109` | ✅ |
| list index | `theorem list_getElem? : Primrec₂ ((·[·]? : List α → ℕ → Option α))` (既定値版 `list_getI [Inhabited α] : Primrec₂ (@List.getI α _)` `:216` / `list_getD (d : α) : Primrec₂ fun l n => List.getD l n d` `:212`) | `:187` | ✅ |
| 補助 | `list_length` `:255` / `list_append` `:219` / `option_getD : Primrec₂ (@Option.getD α)` (Basic `:569`) / `comp` (Basic `:216`) / `const` (Basic `:209`) | — | ✅ |
| unpair | `theorem unpair : Primrec Nat.unpair` / `theorem natPair : Primrec₂ Nat.pair` | `Mathlib/Computability/Primrec/Basic.lean:313` / `:366` | ✅ |
| Primrec→Computable | `theorem Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {f : α → σ} (hf : Primrec f) : Computable f` | `Mathlib/Computability/Partrec.lean:247` | ✅ |
| Option→Partrec | `theorem ofOption {f : α → Option β} (hf : Computable f) : Partrec fun a => (f a : Part β)` | `Mathlib/Computability/Partrec.lean:275` | ✅ |
| **`Primcodable (Finset _)`** | — | — | ❌ **不在** (loogle Found 0) |
| **`Primcodable (Multiset _)`** | — | — | ❌ **不在** (loogle Found 0) |
| **`Primrec` × `encodeNat`** | — | — | ❌ **不在** (loogle Found 0) |

**in-tree の雛形 (loogle-blind ガード: これが「1 本挙げるべき template lemma」)**:
`EntropyRateUpper.lean` が同型の decoder を既に proof-done で持っている —
`typeDecoderOption (m n : ℕ) : Option ℕ` (`:70`) → `typeDecoderOption_computable : Computable fun p : ℕ × ℕ ↦ …`
(`:122`、`Primrec.list_getElem?`/`option_map`/`nat_div`/`nat_mod` の鎖 + `.to_comp`) →
`typeDecoder_partrec : Partrec₂ (typeDecoder (α := α))` (`:162` = `Computable.ofOption …`) → `invariance` へ投入
(`EntropyRate.lean:425`)。**P10 は `List α` を `List ℕ` に替えるだけでこの雛形がそのまま効く**
(グローバル instance で済むので `primcodableOfFintype` (`:48`) のような local instance も不要)。

**本調査の machine 検証 (0 error / 0 sorry)**:

```lean
noncomputable def twoPartDecoderOption (m : ℕ) : Option ℕ :=
  ((decode (α := List ℕ) (Nat.unpair m).1).getD [])[(Nat.unpair m).2]?
-- Computable (8 行) → Partrec₂ (Computable.ofOption) → prefix_invariance に投入して
-- `∃ b, ∀ x q, x ∈ twoPartDecoder (decodeNat q) 0 → prefixComplexity x ≤ 2 * q.length + b` が通る
```

### F. in-tree 第 2 波資産 (read-only 消費、署名変更なし ⟹ consumer ripple 解析不要)

| 資産 | 署名 (verbatim) | file:line | P10 での役割 |
|---|---|---|---|
| K | `noncomputable def prefixComplexity (x : ℕ) : ℕ := sInf { l \| ∃ p : List Bool, p.length = l ∧ x ∈ prefixUniversalEval p }` | `PrefixMachine.lean:280` | `modelComplexity` / MDL の両辺 |
| K 到達性 | `theorem prefixComplexity_spec (x : ℕ) : ∃ p : List Bool, p.length = prefixComplexity x ∧ x ∈ prefixUniversalEval p` | `:288` | 最短 program |
| **K = 2m+1** | `theorem prefixComplexity_eq_two_mul_payloadComplexity_add_one (x : ℕ) : prefixComplexity x = 2 * payloadComplexity x + 1` | `Levin.lean:114` | **汚染会計の全て**。かつ `K ≥ 1` ⟹ 構造関数の k=0 が空集合 (退化境界②) |
| m | `noncomputable def payloadComplexity (x : ℕ) : ℕ := sInf { l \| ∃ d : List Bool, d.length = l ∧ x ∈ decodePayload d }` (上界 `payloadComplexity_le_of_mem {x d} (h : x ∈ decodePayload d) : payloadComplexity x ≤ d.length` `:106`) | `Levin.lean:77` | **加法世界の複雑さ** (crux はここで述べる) |
| **prefix invariance** | `theorem prefix_invariance (A : ℕ → ℕ → Part ℕ) (hA : Partrec₂ A) : ∃ b : ℕ, ∀ (x : ℕ) (q : List Bool), x ∈ A (decodeNat q) 0 → prefixComplexity x ≤ 2 * q.length + b` | `Omega.lean:146` | **infra 無しで取れる版 (Route A) の入口**。`prefix_invariance_code` (`:132`) は `b = 2 * encodeCode c + 5` を明示 |
| interpret 入口 | `def prefixInterpretProg (idx : ℕ) (q : List Bool) : List Bool := selfDelimit (true :: (List.replicate idx true ++ (false :: q)))` / `prefixInterpretProg_length … = 2 * q.length + (2 * idx + 5)` / `prefixUniversalEval_interpret` | `Omega.lean:117` / `:120` / `:126` | crux の program 構成 |
| payload 復号 | `noncomputable def decodePayload : List Bool → Part ℕ` (`[] => none`, `false::bs => some (decodeNat bs)`, `true::bs => eval (ofNat Code (parseUnary bs).1) (Nat.pair (decodeNat (parseUnary bs).2) 0)`) | `PrefixMachine.lean:162` | **crux で自己シミュレーションする対象** |
| 自己限定 / unary parse | `def selfDelimit (bs : List Bool) : List Bool := List.replicate bs.length true ++ false :: bs` / `selfDelimit_length … = 2 * bs.length + 1` / `range_selfDelimit_prefixFree` / `def parseUnary : List Bool → ℕ × List Bool` / `parseUnary_replicate (n) (q) : parseUnary (List.replicate n true ++ (false :: q)) = (n, q)` | `:107` / `:139` / `:143` / `UniversalMachine.lean:38` / `:108` | index の自己限定 (prefix-free 既証明) + crux の parse |
| `entropy` | `noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ` | `InformationTheory/Shannon/Bridge.lean:40` | **P10 では不要** (§14.12 の対象は 1 本の文字列 x についての量で測度が出てこない)。親計画 §Approach の依存表と §Phase P10「依存」から落とすのが正 (child = 本在庫が newer) |

### G. アルゴリズム的統計 (§14.12 そのもの) の Mathlib 在庫

| 不在物 | loogle query | 結果 (verbatim) |
|---|---|---|
| 十分統計量 | `"SufficientStatistic"` | `Found 0 declarations whose name contains "SufficientStatistic".` |
| 構造関数 | `"structureFunction"` | `Found 0 declarations whose name contains "structureFunction".` |
| MDL | `"MinimumDescriptionLength"` | `Found 0 declarations whose name contains "MinimumDescriptionLength".` |
| 記述長 | `"descriptionLength"` | `Found 0 declarations whose name contains "descriptionLength".` |
| K 複雑性 | `"KolmogorovComplexity"` | `Found 0 declarations whose name contains "KolmogorovComplexity".` |
| (広め) | `"Sufficient"` | `Found one declaration whose name contains "Sufficient".` → `Std.Http.Status.insufficientStorage` (無関係) |
| (広め) | `"Kolmogorov"` | `Found 26 declarations` — 全て `ProbabilityTheory.IsKolmogorovProcess` 系 (Kolmogorov 連続性定理、無関係) |

---

## Key-preconditions box (着手前の事故ポイント)

1. **`Encodable.encode (S : Finset ℕ)` を model code に使ってはいけない**。`Primcodable (Finset _)` /
   `Primcodable (Multiset _)` が **両方 Found 0** ⟹ それを復号する decoder は `Computable` を名乗れず
   `Nat.Partrec.Code` に載らない。**model code は `Encodable.encode (S.sort (· ≤ ·)) : ℕ` (= `List ℕ` の符号)**。
   `Finset` は statement 側 (card / membership) にだけ登場させ、計算可能部分には一切入れない。
2. **`Finset.sort` の instance 引数は 4 つ** (`[DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]`)。
   `α = ℕ`, `r = (· ≤ ·)` では全部自動 (machine 確認) だが、`α` を一般化した瞬間に 4 つが署名へ漏れる。
3. **構造関数を `ℕ` 値 `sInf` で定義してはいけない**。`Nat.sInf ∅ = 0` かつ `prefixComplexity ≥ 1`
   (`K = 2m+1`) なので **k = 0 では制約集合が空** ⟹ `h_x(0) = 0` が静かに出て **単調性が偽になる**。
   `ℕ∞` 値で `sInf ∅ = ⊤` を使う (machine 検証済: `structureFunction x 0 = ⊤` が通る)。
   ⟹ ℕ∞ 版では `sInf_le` / `sInf_le_sInf` が **非空性の副条件なしで**使える (Mathlib-shape 上も有利)。
4. **`x ∈ S` を制約から落としてはいけない**。`S = ∅` は `Nat.clog 2 0 = 0` (machine 実測) かつ
   `modelComplexity ∅ = K(0)` = 小定数なので、`x ∈ S` が無いと `h_x(k) ≡ 0` の vacuous 定義になる。
5. **`prefix_invariance` の結論は `2 * q.length + b`** (加法ではない)。infra 無しで得られる bound は必ず
   この 2 倍を被る。**加法にしたいなら「渡すものを payload にする」しかない** (§Phase P8 出口 (i) と同じ構造:
   2 倍は機械の def の性質)。
6. **`natLen 0 = 0` / `Nat.clog 2 1 = 0`** (両方 machine 実測)。singleton モデル・index 0 で項がちょうど消えるので
   MDL 上側 (`mdl x ≤ K(x) + c`) が **factor 汚染ゼロ**で出る。この 2 つの境界値に定式化が依存している。
7. **`Nat.clog_le_clog_of_le` は存在しない** (brief の名前)。単調性は `Nat.clog_mono_right`。

---

## 自作が要る要素 (優先順)

1. **§14.12 の定義群 6 本** (`modelCode` / `modelComplexity` / `twoPartLength` / `mdlComplexity` /
   `structureFunction` / `IsSufficientStatistic`) + 構造的定理 7 本 (単調性 / singleton 崩壊 / sInf 到達性 /
   index 幅 / membership→index)。**見積 ~120 行、本調査で machine 検証済み** (§着手 skeleton をそのまま使える)。
   落とし穴は Key-preconditions ③④。
2. **`natLen` 下界 1 本**: `theorem natLen_lt_two_pow (n : ℕ) : n < 2 ^ natLen n`。**見積 ~10 行**
   (`UniversalMachine.lean:64` の `posLen_le` と同型の `PosNum` 帰納)。これ 1 本から
   `natLen` 単調性 (`a ≤ b → natLen a ≤ natLen b`、1 行、machine 検証済) と
   `natLen (Nat.pair a b) ≤ 2 * natLen (max a b)` が出る。**Route A (下記 4) を採るときだけ必要**。
3. **bit codec の `Primrec` 化 + range 上の逆向き round-trip** (crux の部品、**Mathlib 0 本**):
   `Primrec Computability.decodeNat` / bit 抽出 (`div`/`mod` 経由なら `Primrec.nat_div`/`nat_mod` で済む) /
   `Primrec parseUnary` / **`encodeNat (decodeNat w) = w` (w が `true` で終わるとき)**。
   **見積 60–130 行**。`decodePosNum [false] = 2` なので canonical (末尾 `true`) 制限は必須。
4. **crux = 機械の自己シミュレーション** (共有 sorry 候補):
   ```lean
   theorem payloadComplexity_two_part_le (A : ℕ → ℕ → Part ℕ) (hA : Partrec₂ A) :
       ∃ c : ℕ, ∀ (x y i : ℕ), x ∈ A y i →
         payloadComplexity x ≤ payloadComplexity y + 2 * natLen i + c
   ```
   `decodePayload` を code の中で走らせる (= `Nat.Partrec.Code.eval_part` + 3 の部品)。
   **見積 90–160 行** (3 と合わせて 150–290 行)。**これは P10 の他の全部より重い** ⟹ §Honest scope call。
   **同じ infra が P9 park (`plan:kolmogorov-w2-omega-noncomputable` の候補定式化 (ii)
   `¬ ComputablePred (fun n ↦ (prefixUniversalEval (decode n)).Dom)`) の前提でもある** ⟹ 集約推奨。
5. (Route A、infra 無しで取れる弱い版、**任意**) `Nat.pair` 経路の two-part bound
   `∃ b, ∀ x S i, x ∈ S → K x ≤ 4 * (natLen (modelCode S) + Nat.clog 2 S.card) + b`。**見積 ~40 行**
   (decoder は machine 検証済、2 が必要)。**ただし §Honest scope call (C4) の理由で headline にしてはいけない**。

---

## Mathlib 壁の列挙 (`@residual` 候補)

**genuine な `wall:` は 0 件**。P10 の不在物はすべて (a) 定義の選択 (big) か (b) in-tree infra の自作であり、
「Mathlib に無い解析 (hard)」ではない。親計画 §residual slug 方針の「`wall:` を打つ先は現状無い」を維持する。

| 不在物 | loogle confirmation (verbatim) | 判定 |
|---|---|---|
| `Primcodable (Finset _)` | `Found 0 declarations mentioning Finset and Primcodable. Of these, 0 match your pattern(s).` | **非壁 (設計で回避)**: model code を `List ℕ` 符号にする ⟹ 追加作業 0 |
| `Primcodable (Multiset _)` | `Found 0 declarations mentioning Multiset and Primcodable. Of these, 0 match your pattern(s).` | 同上 |
| `encodeNat` の `Primrec` 性 | `Found 0 declarations mentioning Primrec and Computability.encodeNat.` (`Computability.encodeNat` に付く Mathlib 補題は `Computability.decode_encodeNat` の 1 本のみ) | **非壁 (自作 = 選択)**: §自作 3。template = `EntropyRateUpper.lean:109` `ofDigits_primrec` (同型の `Primrec` 手組み、既に proof-done) |
| `encode` のサイズ補題 | (A 節: Mathlib に 1 本も無い) | **非壁 (設計で回避)**: K(S) で述べればサイズ補題が不要になる |
| §14.12 の全 object | G 節の Found 0 × 5 | **非壁 (定義自作)** |

**共有 sorry-lemma 推奨**: §自作 4 の `payloadComplexity_two_part_le` を
**`@residual(plan:kolmogorov-w2-machine-partrec)` 付きの共有 sorry 補題 1 本に集約することを推奨**
(`docs/audit/audit-tags.md` §Shared Mathlib walls のパターン。class は `wall:` ではなく **`plan:`**)。
理由: (i) P10 の headline 2 本 + `modelComplexity {x} ≤ K(x) + c` が全部これ 1 本に帰着する、
(ii) **P9 park の Ω 非計算性が同じ infra を要求する** ⟹ 2 object が共有する。
**この命題は「真だが未証明」** (§Phase P8 の加法版 Levin と違って真偽不明ではない — 上の pseudo-Lean で
構成が具体的に書けており、詰まるのは `Primrec` 化の手数だけ) ⟹ `@residual` を貼ることは defect でない。

---

## 撤退ラインからの距離

- **R-W2a** (gateway atom) / **R-W2b** (P8 crux): P10 は触らない (どちらも決着済)。
- **親計画 §Phase P10 の「本 Phase 全体が撤退候補 (park slug `plan:kolmogorov-w2-kss`)」: 発動しない見込み**。
  根拠 = 定義群 + 構造的定理 (§自作 1) が **本調査で 0 error / 0 sorry で通っている** (見積 250–500 行のうち
  ~120 行が実質完成)。「1 セッションで定義群を組めない場合は park」という発動条件は満たさない。
- **新しい撤退ライン (提案) R-W2c — crux 単独 park**: §自作 3+4 (150–290 行) が発散した場合、
  **`payloadComplexity_two_part_le` を `sorry` + `@residual(plan:kolmogorov-w2-machine-partrec)` の共有補題
  1 本として残し、それ以外 (定義群 + 構造的定理 + MDL/構造関数の headline 署名) を type-check done で着地させる**。
  縮退出口は sorry のみで、**仮説束ね (`IsSelfSimulationHypothesis` のような述語化) は禁止** —
  crux は明らかに「証明の核」であって regularity precondition ではない。
  Route A (§自作 5) を「弱いが真の版」として同時に入れるのは可 (headline にしない条件付き、§Honest scope call (C4))。

---

## §推奨定義形 (Mathlib-shape-driven)

いずれも **machine 検証済** (§着手 skeleton をそのまま `lake env lean` に通した、0 error / 0 sorry)。
合わせる結論形を各項に明記する。

| 対象 | 推奨署名 | 合わせた結論形 (1–3 本) | 定数/係数の会計 |
|---|---|---|---|
| モデル符号 | `noncomputable def modelCode (S : Finset ℕ) : ℕ := Encodable.encode (S.sort (· ≤ ·))` | `Primcodable.list` + `Primrec.decode` + `Encodable.encodek` (decoder が `decode (α := List ℕ)` を使える形) | 係数なし。`Finset` を計算部分に入れない |
| モデル複雑さ | `noncomputable def modelComplexity (S : Finset ℕ) : ℕ := prefixComplexity (modelCode S)` | `prefixComplexity` (`PrefixMachine.lean:280`) をそのまま被せる | 係数 **1** (§一行サマリの相殺) |
| 二部記述長 | `noncomputable def twoPartLength (S : Finset ℕ) : ℕ := modelComplexity S + 4 * Nat.clog 2 S.card` | `Nat.le_pow_clog` (`Log.lean:441`) + `natLen_le_of_lt_two_pow` (`UniversalMachine.lean:89`) + `prefix_invariance` の `2 * q.length + b` | **`4 *` を定義に明示的に埋め込む**。理由: index は payload 内で `2·natLen i + 1` bit (自己限定)、payload→program で 2 倍 ⟹ `4·⌈log₂|S|⌉`。これを定義に入れると **headline は加法定数のみの汚染**になり bridge 補題が不要 |
| MDL | `noncomputable def mdlComplexity (x : ℕ) : ℕ := sInf { l \| ∃ S : Finset ℕ, x ∈ S ∧ twoPartLength S = l }` | `Nat.sInf_le` / `Nat.sInf_mem` (in-tree `payloadComplexity` と同型の `sInf { l \| ∃ …, … = l }`) | **ℕ で安全** (singleton が常に居るので非空)。`clog 2 1 = 0` ゆえ上側は汚染 0 |
| 構造関数 | `noncomputable def structureFunction (x k : ℕ) : ℕ∞ := sInf { l \| ∃ S : Finset ℕ, x ∈ S ∧ modelComplexity S ≤ k ∧ (Nat.clog 2 S.card : ℕ∞) = l }` | `sInf_le_sInf` (単調性 3 行) / `sInf_le` / `sInf_empty` (k=0 で `⊤`) | **ℕ∞ 必須** (Key-preconditions ③)。k 軸は K 予算 (教科書と同じ)。値は bit 数 |
| 十分統計量 | `def IsSufficientStatistic (c x : ℕ) (S : Finset ℕ) : Prop := x ∈ S ∧ twoPartLength S ≤ prefixComplexity x + c` | 上の `twoPartLength` / `prefixComplexity` | 述語なので係数なし。**c を明示引数にする** (「∃c」を述語内に隠すと最小性の議論が壊れる) |

**なぜ `Nat.clog 2 S.card` か** (textbook の `log|S|` に対して): (i) `Nat.le_pow_clog` の結論形
`x ≤ b ^ clog b x` が `natLen_le_of_lt_two_pow` の仮説形 `x < 2 ^ k` と直結し、index 幅補題が **1 行**になる
(machine 検証済)。(ii) `Real.natCeil_logb_natCast` (`Log/Base.lean:411`) が `⌈logb 2 n⌉₊ = Nat.clog 2 n` を
与えるので、実数形が要求されたら後から等式 1 本で移せる。**実数 `Real.logb` で定義してはいけない** —
index の bit 数は ℕ であり、`Real.logb` 定義だと床/天井の往復で 50–100 行の bridge が生える。

---

## §Honest scope call

**(A) 真・非退化・仮説なしで入るもの** (infra 無し、本調査で machine 検証):
定義 6 本 / `structureFunction_antitone` (k について単調減少) / `structureFunction_zero_of_singleton_budget`
(`modelComplexity {x} ≤ k → h_x(k) = 0`) / `structureFunction x 0 = ⊤` / `mdlComplexity_spec` (sInf 到達性) /
`mdlComplexity_le_of_mem` / `natLen_le_clog_card` / `exists_index_of_mem`。

**(B) 真だが in-tree infra (§自作 3+4) を要するもの** (= 共有 sorry 1 本に帰着):
headline 1 `prefixComplexity_le_twoPartLength` / headline 2 の両側 MDL / `modelComplexity {x} ≤ K(x) + c` /
「モデル符号の取り替えが加法定数で済む」(符号非依存性) / `IsSufficientStatistic` の witness 存在。

**(C) as-framed で偽 / 述べられないもの — 明示的に名指す**:

- **(C1) 教科書の `K(x) ≤ K(S) + log|S| + O(1)` は、この機械では `log|S|` の係数が 1 では取れない**。
  取れるのは `K(x) ≤ K(S) + 4·⌈log₂|S|⌉ + c`。理由は `K = 2·m + 1` が**恒等式**であること
  (`Levin.lean:114`、§settled facts) — index を payload に自己限定で入れる 2 倍と program 化の 2 倍が積になる。
  ⟹ **`twoPartLength` を `K(S) + ⌈log₂|S|⌉` (教科書形) で定義したうえで headline を
  `K(x) ≤ twoPartLength S + c` と書くのは偽** (`3·⌈log₂|S|⌉` の不足)。**係数 4 を定義側に置く**のが唯一の
  honest な回避 (§推奨定義形)。これは §Phase P8 の加法版 Levin と同じ「weaker relative」構造であり、
  **教科書の two-part inequality / MDL 原理と同一視して命名するのは name laundering** (P8 の禁止事項の再演)。
- **(C2) 「minimal sufficient statistic が存在する」を無条件に述べるのは危険**。§14.12 の minimality は
  `K(S)` 最小化であり、`{ k | ∃ S, IsSufficientStatistic c x S ∧ modelComplexity S ≤ k }` の `sInf` は
  ℕ で書くと (C3) と同じ空集合退化を踏む (c が小さいと十分統計量が存在しない)。**`ℕ∞` 値 + c を明示引数**で
  述べ、「存在」は `c` を十分大きく取る形 (`∃ c, ∀ x, ∃ S, IsSufficientStatistic c x S`) にする。
  後者は singleton モデル + (B) の `modelComplexity {x} ≤ K(x) + c` で出る ⟹ **infra 待ち**。
- **(C3) 構造関数を `ℕ` 値で定義した瞬間に単調性が偽**になる (Key-preconditions ③、`h_x(0) = 0` が出る)。
  退化境界 2 種で確認済: **境界① singleton `S = {x}`** → `clog 2 1 = 0` で index 項が消え statement は生きる
  (非退化)。**境界② `k = 0`** → `K ≥ 1` (from `K = 2m+1`) より制約集合が真に空 ⟹ ℕ 版は 0、ℕ∞ 版は ⊤
  (machine 検証済、構造的に異なる 2 例)。**境界③ `S = ∅`** → `clog 2 0 = 0` なので `x ∈ S` を落とすと vacuous。
- **(C4) `natLen (modelCode S)` を「モデル記述長」として使う定式化 (Route A) は真だが退化**。
  machine 実測で 12 要素モデル = 14941 bit ⟹ `K(x) ≤ 4·(natLen (modelCode S) + clog|S|) + b` は
  literal 上界 `K(x) ≤ 2·natLen x + 3` より常に弱く、**両部符号のトレードオフ (§14.12 の主題) を表現しない**。
  入れるのは可だが **headline / `@[entry_point]` にしない** + docstring で「モデル項は最短記述長ではなく
  canonical 符号長である」ことを明示すること。K(S) 版 (B) が入ったら削除候補。
- **(C5) CT §14.12 の `≈` / `+O(1)` の散文部分** (構造関数の「傾き −1 の直線に沿って落ちる」等の図的主張) は
  **定量的命題として述べない**。述べるなら `∃ c, ∀ …` の形に落ちるものだけ。

**壁判定ガード (CLAUDE.md 準拠)**: (C1) の「係数 1 では取れない」は 0-hit ではなく **恒等式
`prefixComplexity_eq_two_mul_payloadComplexity_add_one` からの演算** (machine 資産) に基づく。
(B) の infra 不在は loogle Found 0 (§壁の列挙) **+ 近い結論形の template を 1 本名指し**
(`EntropyRateUpper.lean:109` `ofDigits_primrec` = 同型の手組み `Primrec`、`:122` = `Computable` 昇格、
`Mathlib/Computability/PartrecCode.lean:994` `eval_part` = 自己シミュレーションの核) + **自作行数見積 150–290 行**
を提示済み ⟹ `wall:` ではなく `plan:` と判定。**非壁側のガード**として (A) の 7 定理は実際に compile させた
(prose ではなく compiler による確認) + 退化境界 2 種を代入済 (C3)。

---

## 着手 skeleton (`InformationTheory/Shannon/Kolmogorov/SufficientStatistic.lean` の出だし)

以下は本調査で **0 error / 0 sorry を machine 確認済み** (定義 6 + 定理 7)。`@[entry_point]` の 2 本と
crux は `sorry` + `@residual(plan:kolmogorov-w2-machine-partrec)` で建ててから 1 本ずつ埋める。

```lean
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Equiv.List
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Kolmogorov.Levin

namespace InformationTheory.Kolmogorov

open Encodable

noncomputable def modelCode (S : Finset ℕ) : ℕ := encode (S.sort (· ≤ ·))

noncomputable def modelComplexity (S : Finset ℕ) : ℕ := prefixComplexity (modelCode S)

noncomputable def twoPartLength (S : Finset ℕ) : ℕ :=
  modelComplexity S + 4 * Nat.clog 2 S.card

noncomputable def mdlComplexity (x : ℕ) : ℕ :=
  sInf { l | ∃ S : Finset ℕ, x ∈ S ∧ twoPartLength S = l }

noncomputable def structureFunction (x k : ℕ) : ℕ∞ :=
  sInf { l | ∃ S : Finset ℕ, x ∈ S ∧ modelComplexity S ≤ k ∧ (Nat.clog 2 S.card : ℕ∞) = l }

def IsSufficientStatistic (c x : ℕ) (S : Finset ℕ) : Prop :=
  x ∈ S ∧ twoPartLength S ≤ prefixComplexity x + c

theorem structureFunction_antitone (x : ℕ) {k k' : ℕ} (h : k ≤ k') :
    structureFunction x k' ≤ structureFunction x k := by
  refine sInf_le_sInf ?_
  rintro l ⟨S, hxS, hSk, rfl⟩
  exact ⟨S, hxS, hSk.trans h, rfl⟩

theorem natLen_le_clog_card {S : Finset ℕ} {i : ℕ} (h : i < S.card) :
    natLen i ≤ Nat.clog 2 S.card :=
  natLen_le_of_lt_two_pow i _ (lt_of_lt_of_le h (Nat.le_pow_clog Nat.one_lt_two _))

theorem exists_index_of_mem {S : Finset ℕ} {x : ℕ} (h : x ∈ S) :
    ∃ i, i < S.card ∧ (S.sort (· ≤ ·))[i]? = some x := by
  have hmem : x ∈ S.sort (· ≤ ·) := (Finset.mem_sort _).2 h
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hmem
  exact ⟨i, by rwa [Finset.length_sort] at hi, by rw [List.getElem?_eq_getElem hi, hix]⟩

end InformationTheory.Kolmogorov
```

`Levin.lean` の import で `PrefixMachine` / `UniversalProbability` / `UniversalMachine` は推移的に入る
(`prefix_invariance` を使う段で `import …Kolmogorov.Omega` を追加)。`InformationTheory.lean` への import 行登録も。

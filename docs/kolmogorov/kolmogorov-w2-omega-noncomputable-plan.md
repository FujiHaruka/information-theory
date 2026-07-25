# Ch.14 Kolmogorov 第 2 波 後継 scope: Ω 自体の非計算性 サブ計画

> **Parent**: [`kolmogorov-w2-moonshot-plan.md`](kolmogorov-w2-moonshot-plan.md) §Phase P9 / §residual slug 方針
> (slug `plan:kolmogorov-w2-omega-noncomputable` = 本ファイルの filename stem)
> **Inventory (SoT for the lemma chain)**:
> [`kolmogorov-w2-omega-noncomputable-inventory.md`](kolmogorov-w2-omega-noncomputable-inventory.md)
> (API 26 件の verbatim 署名 / Key-preconditions box / 自作 10 ブロックの見積は在庫が SoT。本計画は
> それを実装 Phase に落とす制御文書で、署名と file:line を二重定義しない)
> **Goal**: Chaitin 定数 Ω が計算可能実数でないこと — `¬ IsComputableENNReal chaitinOmega`
> (`@[entry_point]`)。新規ファイル `InformationTheory/Shannon/Kolmogorov/OmegaNoncomputable.lean`。

## 進捗

- [x] M0 — Mathlib/in-tree API 在庫調査 ✅ →
      [`kolmogorov-w2-omega-noncomputable-inventory.md`](kolmogorov-w2-omega-noncomputable-inventory.md)
- [x] 前哨 gateway atom — 機械の partrec 性 + 停止集合の決定不能性 ✅ (`PrefixComputability.lean`、`4efc230d`)
      ⟹ 親 §settled facts の**候補定式化 (ii) はコード側で closure**。本計画が負うのは **(i) 側 = 計算可能実数の
      定式化 + Chaitin 論法** のみ (§Settled facts の machine entry)
- [ ] **N0 — skeleton + 有界機械 `prefixEvaln`** 📋 (**make-or-break**、gateway atom = `prefixEvaln_primrec`)
- [ ] N1 — ビット列列挙器 📋
- [ ] N2 — 近似列 `omegaApprox` / `omegaApproxNum` + 橋 + 計算可能性 📋
- [ ] **N3 — 下からの近似の完全性 (最重量ブロック)** 📋
- [ ] N4 — 探索 `searchTime` + その計算可能性 📋
- [ ] N5 — 質量超過 + headline 組み立て 📋

---

## ゴール / Approach

### 到達形 (署名は在庫 §到達形 が verbatim SoT)

```lean
def IsComputableENNReal (x : ℝ≥0∞) : Prop := ...   -- 加法形、§定義形の設計
@[entry_point] theorem chaitinOmega_not_computable : ¬ IsComputableENNReal chaitinOmega
```

### 全体戦略 — Chaitin 論法 5 ステップ ↔ Phase 対応

Ω は**下から計算可能に近似できる** (停止した program の質量を積み上げるだけ) が、**上からは近似できない**。
上下両側の近似が揃うと「長さ ≤ n の未停止 program はもう永久に停止しない」という時点を有限時間で確定でき、
停止集合が決定可能になってしまう — これが前哨 gateway atom が閉じた
`prefixUniversalEval_dom_not_computablePred` と矛盾する。

| # | Chaitin 論法のステップ | 負う Phase | 出口 (下流が消費する形) |
|---|---|---|---|
| 1 | **下からの計算可能近似** `Ω_t` (時刻 t までに停止した長さ ≤ t の program の質量) | **N0 → N1 → N2** | `omegaApprox` / `omegaApproxNum` + `Computable omegaApproxNum` |
| 2 | 精度 `2^{-n}` の**二進有理近似** `a n` を仮定側から取る | **N0** (定義のみ) | `IsComputableENNReal` の witness `a : ℕ → ℕ` |
| 3 | `Ω < Ω_t + 2^{-n}` を満たす **t の探索** (計算可能) | **N3 (存在) → N4 (計算可能性)** | `exists_omegaApprox_gt` → `searchTime` |
| 4 | その t 以降、**長さ ≤ n の未停止 program は永久に停止しない** (質量超過) | **N5** | 質量超過補題 |
| 5 | ⟹ 停止性が決定可能 ⟹ **前哨 atom と矛盾** | **N5** | `chaitinOmega_not_computable` |

ステップ 1 と 5 は同じ有界機械 `prefixEvaln` を要する (1 は質量の計算、5 は決定手続きの本体) ⟹
**N0 が全ステップの土台であり make-or-break**。

### 定義形の設計 (Mathlib-shape-driven)

**採用 = 在庫 §C-2 の案 (i) — 計算可能二進有理近似列 + 誤差 `2^{-n}`、分子は ℕ、加法形。**

採用理由 (消費する lemma の結論形に定義を合わせる、CLAUDE.md「Mathlib-shape-driven Definitions」):

- **`Computable.find` (`Mathlib/Computability/RE.lean:177`) の `[DecidableRel P]` に載る形**であること。
  探索述語を ℝ≥0∞ の不等式で書くと古典 instance になり `decide` が計算不能になる ⟹ 述語を **ℕ の dyadic 比較**に
  落とせる定義でなければ Phase N4 が組めない。案 (i) の分子 ℕ 表現はこれに直接載る。
- **ℚ / ℤ の `Primrec` API が Mathlib に丸ごと無い** (§Settled facts の loogle-neg 2 件) ⟹ ℚ を経由する案 (iii) は
  `ComputablePred` を消費する側が原理的に組めない。
- **truncated subtraction を持ち込まない**。加法形にすれば ℝ≥0∞ の引き算は論法全体で
  `ENNReal.sub_lt_self` の 1 箇所 (Phase N3) にしか現れない。

不採用の理由:

- **案 (ii) 二進展開**: 二進展開は二進有理点で一意でない ⟹ Ω の無理数性という**本 scope 外の隠れ依存**を作る。
- **案 (iii) Dedekind 切断の決定可能性**: 上記 ℚ の `Primrec` 不在に加え、古典的にも x が有理のとき
  「切断が決定可能 ⟺ 計算可能」が破れる ⟹ **教科書より強い述語**になる (下記 ⚠️ と同じ罠)。

#### ⚠️ 最大の危険 — 誤差幅を「厳密な床関数」にすると命題が弱くなる

`a n * 2^{-n} ≤ x ≤ (a n + 1) * 2^{-n}` (幅ちょうど `2^{-n}` の両側挟み) という**厳密床形は、標準の計算可能実数の
定義から導けない** — x が格子点 `k·2^{-n}` の近傍にあるとき `a n` を `k-1` と `k` のどちらに出すかは符号判定を
要し、計算可能実数では決定不能だからである。⟹ 厳密床形は**標準より強い述語**であり、その否定は
**教科書の Chaitin 定理より弱い定理**になる。

**採る形は加法形** (`x ≤ a n·2^{-n} + 2^{-n}` かつ `a n·2^{-n} ≤ x + 2^{-n}`、すなわち
`|x - a n·2^{-n}| ≤ 2^{-n}`)。標準の「計算可能有理近似列 `q` で `|x - q n| ≤ 2^{-n}`」から
`a n := round (q m · 2^n)` (m 十分大) で**導ける**向きが立つので、`¬(加法形)` は標準の非計算可能性を含意する
**より強い定理**になる。

**恒久ルール (name laundering 禁止、P8 の factor-2 / P10 の係数 4 と同一構図)**:

1. 着地形が加法形でない (厳密床形など標準より強い述語の否定に落ちた) 場合、**教科書の Chaitin 定理と同一視して
   命名・記述してはならない**。headline 名は述語名を明示した形に留め、module docstring に
   「どの述語の否定であって、標準の計算可能実数とどちらが強いか」を明記する。
2. 加法形で着地した場合も、docstring では「標準定義から本述語が導ける向き」を 1 段落で述べる。
   **標準定義そのものを Lean で書くことは ℚ の `Primrec` 不在ゆえ不可能**なので、この向きの diff は
   paper-level に留まる — だからこそ命名の禁止条件を恒久ルールとして先に固定する (R-ONC3)。
3. **機械検証できる半分は機械で取る**: 厳密床形の述語 → 加法形の述語 が成り立つ (同じ `a` がそのまま witness に
   なる) ので、`isComputableENNReal_of_floor` 相当の含意補題を Phase N5 で 1 本入れれば、
   「我々の `¬` の方が強い」ことがコンパイラ確認済になる (散文の主張をタグではなく定理に落とす)。

#### 対象の型 — どこで型を落とすか

**`chaitinOmega : ℝ≥0∞` のまま扱い、`.toReal` を取らない** (在庫 §D の推奨)。落とす境界は 2 箇所だけ:

- **ℝ≥0∞ → ℕ (分子)**: Phase N2 の橋補題 `omegaApprox t = (omegaApproxNum t : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ t` 1 本。
  `ENNReal.mul_inv_cancel` の両側副条件 (`≠ 0` かつ `≠ ⊤`) はこの補題の中 (~15 行) にだけ閉じ込める。
- **ℝ≥0∞ 述語 → ℕ 述語**: Phase N4 の探索述語の同値補題 1 本 (`Computable.find` の `DecidableRel` 要件)。

割り算 `/` は全体で 1 度も書かない。**ℝ 版 headline (`chaitinOmega.toReal`) は本計画の scope 外** (R-ONC4) —
分子 ℕ の定義を ℝ に持ち込むと `x < 0` で恒偽になり `¬` が負数で自明に真 = 退化定義の濫用に見えるため。

#### 精度会計 (実装前に 1 度 Lean で検算すること)

margin を `m := n + 2` に取ると閉じる (紙上の導出、Phase N4/N5 で機械確認する):

- 探索述語 `P n t :≡ a(n+2)·2^{-(n+2)} ≤ Ω_t + 2^{-(n+1)}` (全て ℕ dyadic 比較に落ちる)。
- **存在**: N3 の `Ω < Ω_t + 2^{-(n+2)}` を取ると `a(n+2)·2^{-(n+2)} ≤ Ω + 2^{-(n+2)} < Ω_t + 2^{-(n+1)}` ⟹ P 成立。
- **結論**: 見つかった t で `Ω ≤ a(n+2)·2^{-(n+2)} + 2^{-(n+2)} ≤ Ω_t + 3·2^{-(n+2)} < Ω_t + 2^{-n}`。
- **矛盾 (ステップ 4)**: 未停止の p (|p| ≤ n) が後で停止するなら `Ω_t + 2^{-n} ≤ Ω_t + 2^{-|p|} ≤ Ω`。
  上の `Ω < Ω_t + 2^{-n}` と衝突する。**加法キャンセルに `omegaApprox t ≠ ⊤` が要る** (有限和なので自明だが
  ℝ≥0∞ では明示補題が要る ⟹ Phase N2 の成果物に含める)。
- margin 3 スロットで足りなければ `n+3` に広げるだけで論法は変わらない (撤退事由にしない)。

### 実装原則

- **Skeleton-driven**: 在庫 §着手 skeleton をそのまま Write して type-check done を確認してから 1 sorry ずつ充填。
  skeleton への delta = `prefixEvaln_primrec` (gateway atom、在庫 skeleton は省略している) /
  `prefixEvaln_dom_iff` / `omegaApprox_ne_top`。
- **既存署名は 1 本も変えない**。唯一既存ファイルに触るのが `payloadDispatch_primrec` の追加
  (`SufficientStatistic.lean`) だが、これは**署名変更ではなく本体の移設** — 詳細と実測 ripple は Phase N0。
- **新規 decl だけで閉じる**: `prefixUniversalEval` を触ると親 §Phase P8 の実測 ripple (21 decl / 3 file) +
  `chaitinOmega` の値自体が変わる ⟹ 本計画では**絶対に触らない**。
- **計算可能性の層は `List`、和の層は `Finset`** (`Primcodable (Finset _)` 不在、在庫 §E)。両者を繋ぐ
  `List.toFinset` の `Nodup` 条件は Phase N1 の成果物で先に用意する。
- **退避出口は `sorry + @residual(plan:kolmogorov-w2-omega-noncomputable)` 一択**。仮説束ね
  (`IsComputableApproxHypothesis` 的な述語に核を詰める) は禁止 (R-ONC3)。

---

## Phase 詳細

各 Phase: 依存 / 成果物 (署名略式) / 見積行数 / gateway atom / proof-log / 撤退ライン。
署名の verbatim と消費先 file:line は在庫が SoT。

| Phase | 内容 | 依存 | 見積 | proof-log | 撤退 |
|---|---|---|---|---|---|
| **N0** | skeleton + 定義 2 本 + 有界機械 `prefixEvaln` (in 在庫 #1–#3) | 前哨 atom | **105–150** | **yes** | R-ONC0 |
| N1 | ビット列列挙器 + `2^n` の Primrec (#4) | N0 | 45–70 | no | — |
| N2 | 近似列 + 橋 + `Computable omegaApproxNum` (#5/#6) | N0, N1 | 100–150 | no | — |
| **N3** | 単調性 + `Ω_t ≤ Ω` + **下からの近似の完全性** (#7、**最重量**) | N2 | **60–100** | **yes** | R-ONC1 |
| N4 | 探索 `searchTime` + 計算可能性 (#8) | N2, N3 | 60–95 | no | R-ONC2 |
| N5 | 質量超過 + headline + 強度 witness (#9/#10) | N0, N3, N4 | 90–140 | no | R-ONC3 |

**合計 460–705 行 / 新規 1 ファイル**。在庫の 400–650 より上振れしているのは
(a) `payloadDispatch_primrec` の移設、(b) `omegaApprox_ne_top`、(c) 強度 witness の 3 点を本計画で追加したため。
**行数は撤退判断の根拠にしない** (親 §Approach「under-estimation ガード」: P8 下振れ / P10 上振れの両方を実測が是正)。

### Phase N0 — skeleton + 有界機械 `prefixEvaln` (make-or-break) 📋

- **依存**: 前哨 gateway atom (`PrefixComputability.lean`) / `decodePayload_eq_dispatch` (`SufficientStatistic.lean:375`) /
  `Nat.Partrec.Code.primrec_evaln` (`Mathlib/Computability/PartrecCode.lean:922`、§Settled facts で verbatim 確認済)。
- **成果物**:
  - `def IsComputableENNReal (x : ℝ≥0∞) : Prop` — §定義形の加法形。
  - `noncomputable def prefixEvaln (k : ℕ) (p : List Bool) : Option ℕ` —
    `decodePayload_eq_dispatch` の `eval` を `evaln k` に置き換えただけの bounded 版。
  - `theorem payloadDispatch_primrec : Primrec payloadDispatch` (**`SufficientStatistic.lean` に追加**)。
  - `theorem prefixEvaln_mono / _sound / _complete` — `evaln_mono` / `evaln_sound` / `evaln_complete` を
    `Option.bind` 越しに lift。
  - `theorem prefixEvaln_dom_iff {p} : (prefixUniversalEval p).Dom ↔ ∃ k, (prefixEvaln k p).isSome`
    (ステップ 5 の決定手続きが消費する形。`_complete` の両向きから)。
  - **gateway atom** `theorem prefixEvaln_primrec : Primrec fun a : ℕ × List Bool ↦ prefixEvaln a.1 a.2`。
- **make-or-break の所在**: 計算可能性の層が組めるかは `prefixEvaln_primrec` 1 本に集約される。
  次点リスクは `prefixEvaln_complete` の**逆向き** (`Dom → ∃ k`)。この 2 本が通れば以降は直線。
- **`payloadDispatch_primrec` の正しい入れ方 (在庫の「~3 行」は過小、verbatim 確認済)**:
  既存 `payloadDispatch_computable` (`SufficientStatistic.lean:347`) の証明本体は 348–373 行の 26 行で、
  最終行が `refine ((Primrec.list_casesOn …).of_eq ?_).to_comp`。⟹ **本体を `payloadDispatch_primrec` に移設し
  (`.to_comp` を落とす)、`payloadDispatch_computable := payloadDispatch_primrec.to_comp` の 1 行に書き換える**のが
  正しい形 (複製は禁止)。**署名は変わらない ⟹ ripple 0**:
  `scripts/dep_consumers.sh InformationTheory.Kolmogorov.payloadDispatch_computable` の実測 =
  **direct consumer 1 decl / 1 file** (`SufficientStatistic.lean:383` `decodePayload_partrec`)。
- **見積**: 105–150 行 (うち `payloadDispatch_primrec` の移設は正味 +4 行)。
- **proof-log: yes** — 有界機械の構成手法は後継 scope `plan:kolmogorov-w2-levin` (加法的普遍 prefix 機械の構成) が
  そのまま再利用する。
- **撤退**: R-ONC0。

### Phase N1 — ビット列列挙器 📋

- **依存**: N0。**成果物**: `allBitStrings` / `allBitStringsLE` (`List.flatMap` 再帰) +
  `mem_allBitStringsLE : p ∈ allBitStringsLE t ↔ p.length ≤ t` + `Nodup` + `Primrec allBitStringsLE` +
  `primrec_two_pow : Primrec fun n : ℕ ↦ 2 ^ n` (雛形 = `primrec_replicate_true` @ `PrefixComputability.lean:27`)。
- **注意**: `List.sections` 経由は Primrec 補題が無いので採らない (在庫 §E)。`Nodup` は N2 の
  `List.toFinset` ↔ `List.sum` の橋を安くするために**先に**建てる。
- **見積**: 45–70 行。**proof-log: no**。**撤退**: なし (詰まる要素が無い)。

### Phase N2 — 近似列 + 橋 + 計算可能性 📋

- **依存**: N0, N1。
- **成果物**:
  - `noncomputable def omegaApprox (t : ℕ) : ℝ≥0∞` — `chaitinOmega` の被加数と**同一形**
    (`(2:ℝ≥0∞)⁻¹ ^ p.length` の `Finset` 和) で建てる。
  - `def omegaApproxNum (t : ℕ) : ℕ` — 分子 (`2 ^ (t - p.length)` の ℕ 和)。
  - `theorem omegaApprox_eq_num (t) : omegaApprox t = (omegaApproxNum t : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ^ t` — **橋 1 本**。
    `ENNReal.mul_inv_cancel` の両側副条件はここに閉じ込める。
  - `theorem omegaApprox_ne_top (t) : omegaApprox t ≠ ⊤` — N5 の加法キャンセルに要る (§精度会計)。
  - `theorem omegaApproxNum_computable : Computable omegaApproxNum`。
- **見積**: 100–150 行。**proof-log: no**。**撤退**: なし (部品は全て既存、詰まっても遅いだけ)。

### Phase N3 — 下からの近似の完全性 (最重量ブロック) 📋

- **依存**: N2。
- **成果物**:
  - `theorem omegaApprox_mono : Monotone omegaApprox` (`evaln_mono` + `Finset.sum_le_sum_of_subset_of_nonneg`)。
  - `theorem omegaApprox_le_chaitinOmega (t) : omegaApprox t ≤ chaitinOmega` (**易方向**、`ENNReal.sum_le_tsum`)。
  - **crux** `theorem exists_omegaApprox_gt {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ t, chaitinOmega < omegaApprox t + ε`。
- **結論形の設計判断**: 在庫は `⨆ t, omegaApprox t = chaitinOmega` (等式) を挙げているが、**下流 (N4) が消費するのは
  片側の近似補題だけ**なので、成果物は上の `exists_omegaApprox_gt` を正とする (等式は任意の bonus)。実装ルートは 2 つ、
  安い方を実装時に採る — いずれも本体は cofinality:
  - **route A**: `ENNReal.tsum_eq_iSup_sum'` (`InfiniteSum/ENNReal.lean:74`) の `hs` に停止時刻の上限を渡し、
    `lt_iSup_iff` + `ENNReal.sub_lt_self` で取り出す。
  - **route B**: `ENNReal.tsum_eq_iSup_sum` (`:71`、in-tree 使用実績あり) で **`Finset` を直接**取り出し、
    その各元の停止時刻の `Finset.image` に `Finset.exists_le` で上限 t を取って `omegaApprox_mono` で押し上げる。
    `ι` 添字の `s` 関数を構成せずに済む分だけ軽い見込み。
- **重い理由**: 部分型 `{p : List Bool // (prefixUniversalEval p).Dom}` 上の `Finset` と `List Bool` 側の `Finset` の
  往復。`Finset.image Subtype.val` の `InjOn` は `PrefixMachine.lean:249` に雛形あり。
  また `evaln` の予算 `k` は**時間ではなくサイズ兼用の単一予算** (在庫 §A の注意) なので、
  「長さ ≤ t」と「予算 t」を同時に満たす t を `max` で 1 回組む必要がある。
- **見積**: 60–100 行。**proof-log: yes** (cofinality テンプレは再利用価値がある)。**撤退**: R-ONC1。

### Phase N4 — 探索 `searchTime` + 計算可能性 📋

- **依存**: N2 (分子表現), N3 (存在)。
- **成果物**: ℕ dyadic の探索述語 + `DecidableRel` instance が素直に付く形の定義 / ℝ≥0∞ 版との同値補題 /
  `searchTime` (`Nat.find`) / `Computable searchTime` (`Computable.find` @ `Mathlib/Computability/RE.lean:177`) /
  `chaitinOmega < omegaApprox (searchTime …) + (2:ℝ≥0∞)⁻¹ ^ n`。
- **事故ポイント**: `Computable.find` の `[DecidableRel P]` は**インスタンス引数**。述語を ℝ≥0∞ の不等式で書くと
  古典 instance が付いて `decide` が計算不能になる ⟹ **述語は ℕ dyadic 比較で定義し、ℝ≥0∞ 版とは別補題で同値を取る**
  (在庫 §Key-preconditions box)。margin は `n+2` (§精度会計)。
- **見積**: 60–95 行。**proof-log: no**。**撤退**: R-ONC2。

### Phase N5 — 質量超過 + headline 📋

- **依存**: N0 (`prefixEvaln_dom_iff`), N3, N4。
- **成果物**:
  - 質量超過補題: 未停止 (`(prefixEvaln t p).isSome = false`) かつ `(prefixUniversalEval p).Dom` なら
    `omegaApprox t + (2:ℝ≥0∞)⁻¹ ^ p.length ≤ chaitinOmega` (`Finset.sum_insert` + `ENNReal.sum_le_tsum`)。
  - 決定手続き: `(prefixUniversalEval p).Dom ↔ (prefixEvaln (searchTime … p.length) p).isSome`。
  - **headline** `@[entry_point] theorem chaitinOmega_not_computable : ¬ IsComputableENNReal chaitinOmega` —
    矛盾先は `prefixUniversalEval_dom_not_computablePred` (`PrefixComputability.lean:66`)。
  - **強度 witness (推奨、~10 行)**: 厳密床形 → 加法形 の含意補題 (§定義形の設計 恒久ルール 3)。
- **見積**: 90–140 行。**proof-log: no**。**撤退**: R-ONC3 (署名凍結)。

### 着地後の配線

新ファイル追加につき `InformationTheory.lean` の Kolmogorov 群 (現状 L120–L132) に import 行を追加する。
親 §ファイル構成の「Ω 自体の非計算性は後継 scope の新ファイルへ」がここで確定する。

---

## 撤退ライン (frozen slug)

在庫 §退避候補の 4 段 + 判定基準を採否判断して登録。frozen につき決着後も register に残す。
**退避出口は全て `sorry + @residual(plan:kolmogorov-w2-omega-noncomputable)`**。

- **R-ONC0** (**採用**、Phase N0 = 在庫の判定基準を撤退ラインへ昇格): **発動条件** = `prefixEvaln` の構成と
  `prefixEvaln_primrec` が 1 leg で通らない。**退避** = Chaitin 論法本体に進まず、通った分の `prefixEvaln` 群だけを
  proof-done で残し、headline `chaitinOmega_not_computable` は `sorry` + 本 slug で type-check done に留める。
  **残る honest な着地点** = 有界機械 `prefixEvaln` + sound/mono/complete が計算可能性インフラとして単体で価値を持ち、
  後継 scope `plan:kolmogorov-w2-levin` (機械の建て替え) がそのまま再利用する。
- **R-ONC1** (**採用**、Phase N3): **発動条件** = cofinality (`exists_omegaApprox_gt`) が route A/B とも閉じない。
  **退避** = `exists_omegaApprox_gt` の body のみ `sorry`。`omegaApprox_mono` / `omegaApprox_le_chaitinOmega` の
  **易方向は proof-done を確定**させる。**残る honest な着地点** = 「Ω を下から計算可能に近似する列の構成」が
  完成し、残 residual が 1 補題に局所化される (N4/N5 は N3 を consume するので sorryAx は伝播するが、body 自体は
  honest な組立のまま)。
- **R-ONC2** (**採用**、Phase N4): **発動条件** = `Computable.find` の `DecidableRel` / `decide` の展開で
  `Computable searchTime` が閉じない。**退避** = 存在 (`∃ t, …`) は非構成的に取れるので `Computable searchTime` の
  body だけ `sorry`。**残る honest な着地点** = 「Ω が計算可能なら停止集合が*算術的に*決定される」までの数学的骨格
  (質量超過 + 矛盾の形) が proof-done で残り、欠けているのは決定手続きの実効性 1 点だと明示できる。
- **R-ONC3** (**採用、恒久 = 撤退ではなく禁止事項**、全 Phase): **headline の署名を最後まで崩さない**。
  `¬ IsComputableENNReal chaitinOmega` の核を `IsComputableApproxHypothesis` 的な述語に詰めて仮説で渡す
  (load-bearing bundling) / `Prop := True` 的な退化定義に逃げる / 厳密床形に切り替えたまま教科書 Chaitin 定理として
  命名する (name laundering) — いずれも禁止。**残る honest な着地点** = どこまで進んでも「述語の否定は述べてあり、
  証明の欠落は `sorry` として compiler-visible」という状態が保たれる。
- **R-ONC4** (**不採用 = scope 外の任意拡張として登録**): ℝ 版 headline
  `¬ IsComputableReal chaitinOmega.toReal` + 橋補題。**理由** = 退避候補ではなく追加成果であり、分子 ℕ 定義を ℝ に
  持ち込むと負数で `¬` が自明に真になる符号の縮退リスクがある (在庫 §C-2 ⚠️)。**ℝ≥0∞ 版が proof-done になってから**
  別 leg で検討する。本計画の proof-done 判定に含めない。

**発動見込み**: R-ONC0 = 低〜中 (部品は全て既存だが `payloadDispatch` の Primrec 移設と `evaln` の
`Option.bind` 越し lift が未実測) / R-ONC1 = **中 (最有力)** / R-ONC2 = 低〜中 / R-ONC3 = 恒久。

---

## Settled facts (confidence + 再検証コマンド)

`docs/kolmogorov/kolmogorov-facts.md` は未作成につき本節に保持。散文で「壁である/ない」を主張せず、
再検証で決着させる。

- **前哨 gateway atom が着地している** (confidence = `machine`、commit `4efc230d`):
  `PrefixComputability.lean` の `prefixUniversalEval_partrec` / `prefixUniversalEval_dom_not_computablePred`
  (`@[entry_point]`) を含む 4 decl。⟹ 親 §settled facts の**候補定式化 (ii) はコード側で closure 済**であり、
  本計画が負うのは **(i) 側 = 計算可能実数の定式化 + Chaitin 論法**のみ。
  - 再検証: `lake env lean InformationTheory/Shannon/Kolmogorov/PrefixComputability.lean` +
    `#print axioms InformationTheory.Kolmogorov.prefixUniversalEval_dom_not_computablePred`
- **`primrec_evaln` は存在し型クラス前提を持たない** (confidence = `machine`、オーケストレーター独立確認):
  `theorem primrec_evaln : Primrec fun a : (ℕ × Code) × ℕ => evaln a.1.1 a.1.2 a.2`
  @ `Mathlib/Computability/PartrecCode.lean:922`。⟹ ステップ 1 の計算可能性に**自作は要らない**。
  - 再検証: `rg -n "theorem primrec_evaln" .lake/packages/mathlib/Mathlib/Computability/PartrecCode.lean`
- **ℚ 上に `Primrec` API が無い** (confidence = `loogle-neg`、オーケストレーター独立確認、exit 0 = タイムアウトでない):
  loogle `"Primrec, Rat"` → `Found 0 declarations mentioning Rat and Primrec.`
  ⟹ **近似列は ℚ でも ℤ でもなく ℕ 分子の二進有理数で建てる** (判断ログ #1)。
  - 再検証: `./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Primrec, Rat"`
- **Mathlib に計算可能実数 / 計算可能解析の資産が無い** (confidence = `loogle-neg`、在庫 §C-1 が verbatim SoT):
  `Computable, Real` / `Primrec, Real` / `Computable, Rat` / `Primrec, Int` が全て Found 0、
  `ComputableReal` は `unknown identifier`。in-project 側も 0 hit (`cause:loogle-blind` ガード通過済)。
  **genuine `wall:` は 0 件** — 不足は語彙 (定義の選択 = big) であって解析 (hard) ではない ⟹ 親の `plan:` 分類を追認。
  - 再検証: 在庫 §C-1 の表のクエリを loogle に再投入 + `rg -n "IsComputable|ComputableReal" InformationTheory/`
- **`payloadDispatch_computable` の consumer は 1 decl / 1 file** (confidence = `machine`):
  `SufficientStatistic.lean:383` `decodePayload_partrec` のみ。⟹ Phase N0 の本体移設 (署名不変) は ripple 0。
  - 再検証: `scripts/dep_consumers.sh InformationTheory.Kolmogorov.payloadDispatch_computable`

---

## 判断ログ

1. **近似列は ℕ 分子の二進有理数で建てる (ℚ / ℤ を使わない)**: `Primcodable ℚ` は `Denumerable ℚ` 経由で
   instance としては存在するが、符号化が `Denumerable.ofEncodableOfInfinite` = 不透明な順序同型で、四則の `Primrec` 性が
   事実上証明不能。ℚ / ℤ の `Primrec` API は Mathlib に 0 件 (§Settled facts)。Chaitin 論法は**分母が常に 2 冪**なので
   一般有理数を持ち込む理由も無い ⟹ **分母を `2^n` に固定し分子 ℕ だけを計算可能対象にする**。
   この型選択が §定義形の設計 (案 (i) 採用) と Phase N2/N4 の形を決めている。
2. **定義は加法形、厳密床形にしない (強度の罠)**: 厳密床形は標準の計算可能実数より**強い述語**で、その否定は
   教科書命題より**弱い定理**になる (§定義形の設計 ⚠️)。加法形なら標準定義から導ける向きが立ち、`¬` が標準の
   非計算可能性を含意する。**着地形が弱い版になった場合は教科書 Chaitin 定理として命名しない**恒久ルールを
   R-ONC3 に登録済 — P8 の factor-2 / P10 の係数 4 と同一構図。機械検証できる半分 (厳密床 → 加法形) は
   Phase N5 の witness 補題でコンパイラに確認させる。
3. **対象は `chaitinOmega` (ℝ≥0∞) のまま、`.toReal` を取らない**: 加法形で組めば truncated subtraction は
   `ENNReal.sub_lt_self` の 1 箇所 (Phase N3) にしか現れず、ℝ へ落とす境界が不要。落とすのは ℕ 分子への橋
   (Phase N2) と探索述語の同値 (Phase N4) の 2 箇所のみ。ℝ 版 headline は符号の縮退リスクゆえ scope 外 (R-ONC4)。
4. **Phase N3 の成果物は等式 `⨆ = Ω` ではなく片側の近似補題**: 下流 (N4) が消費するのは
   `∃ t, Ω < Ω_t + ε` だけであり、等式を経由すると `ι` 添字の `s` 関数構成という余分な obligation が付く
   (Mathlib-shape-driven: 消費側の形に合わせる)。等式は任意の bonus として後から導出可能。
5. **`payloadDispatch_primrec` は複製でなく本体移設で入れる**: 在庫の「`.to_comp` を外して 1 本足すだけ (~3 行)」は
   過小 — 実物の証明本体は 26 行あり、複製すると同じ証明が 2 本になる。**本体を Primrec 版に移し
   `payloadDispatch_computable` を 1 行の `.to_comp` に書き換える**。署名不変ゆえ consumer ripple は 0 (実測、§Settled facts)。
6. **proof-log の取得漏れを繰り返さない**: 親の P8 / P10 はいずれも `proof-log: yes` 指定のまま未取得で流れた。
   本計画で `yes` を指定するのは N0 / N3 の 2 つだけに絞り、**Phase 完了時に取得しない判断をしたならその旨を
   本節に 1 行で残す** (無言で流さない)。

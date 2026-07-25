# Ch.14 Kolmogorov 第 2 波 後継 scope: Ω 自体の非計算性 サブ計画 ✅ CLOSURE

> **Parent**: [`kolmogorov-w2-moonshot-plan.md`](kolmogorov-w2-moonshot-plan.md) §Phase P9 / §residual slug 方針
> (slug `plan:kolmogorov-w2-omega-noncomputable` = 本ファイルの filename stem)
> **Inventory**: [`kolmogorov-w2-omega-noncomputable-inventory.md`](kolmogorov-w2-omega-noncomputable-inventory.md)
> (着手前の API 台帳。**着地後は code が SoT** — 署名は `scripts/sig_view.ts` で都度確認し、本計画に verbatim を
> 二重定義しない)
> **Goal (達成)**: `@[entry_point] theorem chaitinOmega_not_computable : ¬ IsComputableENNReal chaitinOmega`
> — **仮説ゼロ (無条件)**。ファイル `InformationTheory/Shannon/Kolmogorov/OmegaNoncomputable.lean`。

## 進捗 — 全 Phase proof-done ✅

- [x] M0 — Mathlib/in-tree API 在庫調査 ✅ → 在庫 (上記リンク)
- [x] 前哨 gateway atom — 機械の partrec 性 + 停止集合の決定不能性 ✅ (`PrefixComputability.lean`、`4efc230d`)
- [x] N0 — skeleton + 有界機械 `prefixEvaln` + `prefixEvaln_primrec` ✅ (`cea4d851`)
- [x] N1 + N2 — ビット列列挙器 / 近似列 `omegaApprox` + 分子の計算可能性 ✅ (`c2ddd7da`)
- [x] N3 + N4 — 単調性 + `iSup_omegaApprox` + 探索 `searchTime` の計算可能性 ✅ (`cce9927a`)
- [x] N5 — 質量超過 + headline + 強度 witness ✅ (`7ea3eb26`)
- [x] 2 ゲート — honesty (`b71cdcc4` / `6624e2f8`、`@audit:ok` 4 件) / style (`20a4a9ac`、PASS・flag-only 0) ✅

**control state (cold-read 用)**: **本計画は closure**。N0–N5 全段が proof-done で着地し、headline は仮説ゼロ。
**撤退ラインは 4 段とも未発動** (§撤退ライン)。既存署名の変更は 0 (唯一の既存ファイル編集 =
`SufficientStatistic.lean` の `payloadDispatch` 本体移設、署名不変 ⟹ ripple 0)。
**残っている任意タスクは proof-log 2 本の未取得のみ** (§判断ログ #6)。sorry / axiom 状態は本計画に焼き込まず
`rg "sorry|@residual" InformationTheory/Shannon/Kolmogorov/OmegaNoncomputable.lean` +
`#print axioms InformationTheory.Kolmogorov.chaitinOmega_not_computable` で都度確認する。
後継 scope として残るのは親の `plan:kolmogorov-w2-levin` (加法版 Levin) 1 件のみ。

---

## ゴール / Approach (着地形)

### Chaitin 論法 5 ステップ ↔ Phase 対応 (着地したまま保持)

Ω は**下から計算可能に近似できる**が、**上からは近似できない**。上下両側の近似が揃うと「長さ ≤ n の未停止
program はもう永久に停止しない」時点を有限時間で確定でき、停止集合が決定可能になる — これが前哨 gateway atom の
`prefixUniversalEval_dom_not_computablePred` (`PrefixComputability.lean`) と矛盾する。

| # | Chaitin 論法のステップ | 負った Phase | 着地した出口 |
|---|---|---|---|
| 1 | 下からの計算可能近似 `Ω_t` | N0 → N1 → N2 | `omegaApprox` / `omegaApproxNum` + `omegaApproxNum_computable` |
| 2 | 精度 `2^{-n}` の二進有理近似を仮定側から取る | N0 | `IsComputableENNReal` の witness `a : ℕ → ℕ` |
| 3 | `Ω < Ω_t + 2^{-n}` を満たす t の探索 (計算可能) | N3 → N4 | `iSup_omegaApprox` / `exists_omegaApprox_gt` → `searchTime_computable` |
| 4 | その t 以降、長さ ≤ n の未停止 program は永久に停止しない | N5 | `omegaApprox_add_le_chaitinOmega` |
| 5 | ⟹ 停止性が決定可能 ⟹ 前哨 atom と矛盾 | N5 | `dom_iff_prefixEvaln_find_isSome` → headline |

**N0 が make-or-break だった** (ステップ 1 と 5 が同じ有界機械 `prefixEvaln` を要する) — 実測でも 1 leg で通過。

### 定義形 — 加法形採用 + 強度を機械で確認済 (恒久ルール)

`IsComputableENNReal` は**加法形** (`|x - a n·2^{-n}| ≤ 2^{-n}` を両側の `≤` で述べ、truncated subtraction を
持ち込まない)。厳密床形 `IsFloorComputableENNReal` は**より強い述語**であり、その否定はより弱い定理になる。

**散文の強度主張を定理に落とした**: `isComputableENNReal_of_floor` (床形 ⟹ 加法形) が入っているので、
「我々の `¬` の方が強い」がコンパイラ確認済。逆向き (加法形 ⟹ 床形) は一様には存在しない (近似列だけから
x が二進格子点のどちら側かを決めることになる) — この非存在の説明も code docstring が持つ。

**恒久ルール (name laundering 禁止、R-ONC3)**: 本 headline は**述語 `IsComputableENNReal` の否定**であって、
教科書の Chaitin 定理と同一視して命名・記述しない。標準の計算可能実数述語との diff (下記 §Settled facts の
2 entry) は module docstring が明示的に持つ。P8 の factor-2 / P10 の係数 4 と同一構図。

### 型と境界 (着地形)

`chaitinOmega : ℝ≥0∞` のまま扱い `.toReal` を取らない。ℕ へ落とす境界は 2 箇所のみ (N2 の橋補題 /
N4 の探索述語の同値)。割り算 `/` は全体で 1 度も書いていない。ℝ 版 headline は scope 外のまま (R-ONC4)。

---

## Phase 実績 (1 行圧縮) + 見積との差分

| Phase | 着地物 | commit | 見積 | 実績 (commit diff) |
|---|---|---|---|---|
| N0 | `IsComputableENNReal` / `IsFloorComputableENNReal` / `prefixEvaln` + mono/sound/complete + **`prefixEvaln_primrec`**、`payloadDispatch_primrec` を `SufficientStatistic.lean:347` に移設 | `cea4d851` | 105–150 | 115 (+ 既存ファイル 7 行) |
| N1+N2 | `allBitStrings(LE)` + `Nodup` + `primrec_two_pow` / `omegaApprox` / `omegaApproxNum` + 橋 + `omegaApproxNum_computable` | `c2ddd7da` | 145–220 | 165 |
| N3+N4 | `omegaApprox_mono` / `iSup_omegaApprox` / `exists_omegaApprox_gt` / `searchPred` + `searchTime` + `searchTime_computable` | `cce9927a` | 120–195 | **209 (上振れ)** |
| N5 | `omegaApprox_add_le_chaitinOmega` / `dom_iff_prefixEvaln_find_isSome` / **headline** / `isComputableENNReal_of_floor` | `7ea3eb26` | 90–140 | **90 net = 下振れ** (+106 / −16、decl 部 73 行) |

**合計**: 新規 1 ファイル 601 行 / 52 decl + `PrefixComputability.lean` 85 行 / 4 decl。**見積 460–705 の範囲内**。

**差分の所在 (この 1 箇所に集約、Phase ごとに散らさない)**: 上振れは **N4** (探索段、~111 行 vs 見積 60–95) —
`Computable.find` の `DecidableRel` を満たす ℕ dyadic 述語と ℝ≥0∞ 版の同値取りが見積より嵩んだ。下振れは
**N5** (decl 部 73 行 vs 見積 90–140) — 質量超過と決定手続きが N0 の `prefixEvaln_dom_iff` / N3 の片側近似補題を
そのまま消費でき、組み立てが薄く済んだ。**最重量と見ていた N3 は見積内**で、重さは実際には N4 に寄っていた。
⟹ 親 §Approach「under-estimation ガード」に整合 (P8 下振れ / P10 上振れに続き、**行数見積は着地の可否も
重さの所在も予言しない**)。

**着地後の配線**: `InformationTheory.lean` の Kolmogorov 群に import 済 (`cea4d851`)。

---

## 撤退ライン (frozen slug) — 4 段とも未発動

frozen につき決着後も register に残す (他文書が slug を参照しうる)。退避出口は全て
`sorry + @residual(plan:kolmogorov-w2-omega-noncomputable)` と定めていたが、**4 段とも使わずに着地した**。
本 slug の残置状況は散文に焼き込まず `rg "@residual\(plan:kolmogorov-w2-omega-noncomputable\)" InformationTheory/`
で都度確認する。

- **R-ONC0** (Phase N0、`prefixEvaln_primrec` が 1 leg で通らない場合の縮退): **未発動** —
  gateway atom `prefixEvaln_primrec` と次点リスク `prefixEvaln_complete` の逆向きが同 leg で通った。
- **R-ONC1** (Phase N3、cofinality `exists_omegaApprox_gt` が閉じない場合の 1 補題 park): **未発動** —
  最有力と見ていたが、等式 `iSup_omegaApprox` まで含めて閉じた (片側補題のみの縮退は不要だった)。
- **R-ONC2** (Phase N4、`Computable searchTime` が閉じない場合の body 単独 park): **未発動** — 述語を ℕ dyadic 比較で
  定義し ℝ≥0∞ 版と別補題で同値を取る設計がそのまま通った (見積は上振れしたが退避事由にはならなかった)。
- **R-ONC3** (**恒久 = 撤退ではなく禁止事項**、全 Phase): headline の署名を崩さない (load-bearing bundling /
  `Prop := True` / 床形のまま教科書 Chaitin 定理として命名する name laundering の禁止)。**未発動かつ恒久的に有効** —
  着地形は加法形の否定であり、honesty ゲートが署名を独立確認済 (`@audit:ok`)。
- **R-ONC4** (**不採用 = scope 外の任意拡張**): ℝ 版 headline `¬ IsComputableReal chaitinOmega.toReal` + 橋補題。
  分子 ℕ 定義を ℝ に持ち込むと負数で `¬` が自明に真になる符号の縮退リスクがあるため、着手するなら別 leg。
  本計画の proof-done 判定には含めない (**closure 後も未着手のまま**)。

---

## Settled facts (confidence + 再検証コマンド)

`docs/kolmogorov/kolmogorov-facts.md` は未作成につき本節に保持。再検証が高価なものだけを残す。

- **標準の計算可能実数述語は Lean で「述べられる」** (confidence = `machine`、独立 honesty 監査がコンパイラで確認、
  `6624e2f8`): `ℚ` は `Denumerable ℚ` (`Mathlib/Data/Rat/Denumerable.lean:30`
  `instance instDenumerable : Denumerable ℚ := ofEncodableOfInfinite ℚ`) 経由で `Primcodable`
  (`Mathlib/Computability/Primrec/Basic.lean:139`
  `instance (priority := 10) ofDenumerable (α) [Denumerable α] : Primcodable α`) ⟹ 「計算可能有理近似列 `q` で
  `|x - q n| ≤ 2^{-n}`」は import 1 行で elaborate する。
  - ⚠️ **旧記述の訂正**: 本計画は以前「標準定義そのものを Lean で書くことは ℚ の `Primrec` 不在ゆえ**不可能**」と
    書いており、これは**誤り**だった (docstring にも伝播、`20a4a9ac` で是正済)。**塞がっているのは「述べること」
    ではなく「含意を証明すること」**。CLAUDE.md「見つけた資産に対する未検証の否定主張」の再演。
  - 再検証: `#synth Primcodable ℚ` を含む scratch ファイル (`import Mathlib.Computability.Primrec.Basic` +
    `import Mathlib.Data.Rat.Denumerable`) を `lake env lean` に通す。
- **`ℚ` / `ℤ` 上の `Primrec` 算術 API は Mathlib に無い** (confidence = `loogle-neg`、2026-07-25 再確認、exit 0):
  loogle `Primrec, Rat` → `Found 0 declarations mentioning Rat and Primrec.` / `Primrec, Int` → 同様に Found 0。
  ファイル走査でも `Mathlib/Computability/` に `ℚ`/`Rat` の言及は **0 ファイル**、`ℤ`/`Int` は 3 ファイル
  (`TuringMachine/Tape.lean` / `TuringMachine/PostTuringMachine.lean` / `AkraBazzi/GrowsPolynomially.lean`) あるが
  **いずれも `Primrec` を 1 度も含まない** (テープ添字と解析、算術 API ではない)。
  - ⟹ **上の machine entry と混同しないこと**: 述語は述べられるが、「標準述語 ⟹ `IsComputableENNReal`」の
    含意証明は丸めに ℚ 上の計算可能除算を要し、この loogle-neg が塞ぐ。近似列を **ℕ 分子の二進有理数**で建てた
    のもこの entry が理由 (§判断ログ #1)。
  - 再検証: `./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Primrec, Rat"`
    (同 `"Primrec, Int"`) + `rg -l "ℚ|\bRat\b" .lake/packages/mathlib/Mathlib/Computability/`
- **Mathlib に計算可能実数 / 計算可能解析の資産が無い** (confidence = `loogle-neg`、在庫 §C-1 が verbatim SoT):
  `Computable, Real` / `Primrec, Real` / `Computable, Rat` が全て Found 0、`ComputableReal` は `unknown identifier`。
  in-project 側も 0 hit (`cause:loogle-blind` ガード通過済)。**genuine `wall:` は 0 件** — 不足は語彙 (定義の選択 =
  big) であって解析 (hard) ではない ⟹ 親の `plan:` 分類は実測で追認された。
  - 再検証: 在庫 §C-1 の表のクエリを loogle に再投入 + `rg -n "IsComputable|ComputableReal" InformationTheory/`
- **`primrec_evaln` は存在し型クラス前提を持たない** (confidence = `machine`):
  `theorem primrec_evaln : Primrec fun a : (ℕ × Code) × ℕ => evaln a.1.1 a.1.2 a.2`
  @ `Mathlib/Computability/PartrecCode.lean:922`。⟹ 有界機械の計算可能性に自作は要らなかった。
  **後継 scope `plan:kolmogorov-w2-levin` (加法的普遍 prefix 機械の dovetail 構成) が同じ資産を消費する見込み**。
  - 再検証: `rg -n "theorem primrec_evaln" .lake/packages/mathlib/Mathlib/Computability/PartrecCode.lean`

---

## 判断ログ

決着済 entry は削除 (git が履歴)、恒久ルール / 未回収の obligation のみ残す。

1. **近似列は ℕ 分子の二進有理数で建てる (ℚ / ℤ を使わない) — 恒久**: `Primcodable ℚ` は instance として存在するが
   符号化が `Denumerable.ofEncodableOfInfinite` = 不透明な順序同型で、四則の `Primrec` 性が事実上証明不能
   (§Settled facts の loogle-neg entry)。Chaitin 論法は分母が常に 2 冪なので一般有理数を持ち込む理由も無い。
   **後続で計算可能実数の語彙を拡張する場合もこの型選択を出発点にする** (ℚ 経由に切り替えるなら `Primrec` 算術の
   自作が先立つ)。
2. **定義は加法形、厳密床形にしない — 恒久 (R-ONC3 と対)**: 床形は標準より強い述語で、その否定は教科書命題より
   弱い定理になる。**着地形を教科書 Chaitin 定理として命名しない**禁止は恒久的に有効。機械検証できる半分
   (床形 ⟹ 加法形) は `isComputableENNReal_of_floor` として入っており、散文でなく定理が強度を保証する。
3. **未検証の否定主張を plan に書かない — 恒久 (本計画で実際に踏んだ)**: 「標準述語は Lean で述べられない」は
   コンパイラに 1 行も通さずに書かれた否定主張で、独立監査が反証した (§Settled facts)。**資産の非存在を主張する
   なら loogle-neg か machine のどちらの confidence なのかを明示し、両者を 1 文に混ぜない。**
6. **proof-log 2 本が未取得 (唯一の残タスク、任意)**: N0 (有界機械 `prefixEvaln` の構成手法) と N3 (cofinality
   テンプレ) に `proof-log: yes` を指定していたが**未取得のまま closure した**。親 P8 / P10 と同じ扱い。
   N0 の手法は後継 scope `plan:kolmogorov-w2-levin` (機械の建て替え) が再利用しうるので、回収するなら
   `docs/proof-logs/proof-log-kolmogorov-w2-omega-noncomputable.md` として後続 leg で。
   (番号 4/5 は決着済につき削除。他文書参照を壊さないため振り直さない。)

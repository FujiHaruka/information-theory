# Ch.14 Phase P8 — prefix 複雑さと普遍確率の factor-2 関係 Lean 形式化 — ボトルネック分析

将来「命題の形をコードから逆算する支援ツール」および「Mathlib / in-tree 補題検索ツール」を作るためのベースライン記録。

**定量データ**: [docs/metrics/kolmogorov-w2-p8-levin.metrics.md](../metrics/kolmogorov-w2-p8-levin.metrics.md)

対象コミット: `6861eb14` (実装) / `be6d1f7f` (honesty ゲート) / `07acd1c0` (style ゲート)。
親計画: [docs/kolmogorov/kolmogorov-w2-moonshot-plan.md](../kolmogorov/kolmogorov-w2-moonshot-plan.md) §Phase P8。

---

## 0. 対象問題と成果物

**着手時の目標**: Cover-Thomas §14.6 の Levin 符号化定理（加法版）

```
∃ c, ∀ x, |K(x) + log₂ P_U(x)| ≤ c
```

**実際に着地した命題**: 同じ機械 `prefixUniversalEval` に対して真な factor-2 版

```
-log₂ P_U(x) ≤ K(x) ≤ 2·(-log₂ P_U(x)) + 1
```

下半分は P7 の `neg_logb_universalProb_le_prefixComplexity` で既に取得済みだったので、P8 が入れたのは上半分。

成果物:

- `InformationTheory/Shannon/Kolmogorov/Levin.lean` — 新規 16 decl、0 sorry / 0 `@residual`（現在 255 行、ゲートの docstring 追記込み）
  - headline `prefixComplexity_le_two_mul_neg_logb_universalProb`（`@[entry_point]`、仮説なし）
  - 支柱 2 本 `prefixComplexity_eq_two_mul_payloadComplexity_add_one`（構造恒等式）/ `universalProb_le_two_pow_neg_payloadComplexity`（数え上げ上界）
- `InformationTheory/Shannon/Kolmogorov/PrefixMachine.lean` — Kraft 不等式を「この機械の受理集合」から「任意の prefix-free 集合」へ一般化（`PrefixFree.kraft` / `PrefixFree.tsum_inv_two_pow_length_le_one` / `selfDelimit_length` の 3 decl 追加）
- 全 decl が `#print axioms` で標準 3 公理のみ

---

## 1. 問題のキャラクター

**この leg の支配項は補題探索でもタクティクでもなく、「証明すべき命題の形を決めること」だった。**
形が決まった後の証明は数え上げ 1 本で、dead end は無い（`lake env lean` の回数内訳は metrics 側）。

計画は着手前この Phase を「第 2 波唯一の真の crux」「200–400 行、Shannon-Fano-Elias 逆向き構成」と見積もっていた。
実測はその下側 242 行で、しかも SFE 構成は 1 行も書いていない。見積が外れた原因は行数の読み違いではなく、
**証明対象の命題が着手前に確定していなかった**こと（教科書の加法版が、この機械に対して真かどうか未確定だった）。

同家系の Phase P10 との対比（[proof-log-kolmogorov-w2-p10-kss.md](proof-log-kolmogorov-w2-p10-kss.md)）:

| | P8 | P10 |
|---|---|---|
| 支配項 | 命題の形の決定 | 定義形の決定 + computability infra の手組み |
| Mathlib 探索コスト | ほぼゼロ（loogle 1 回） | 中（在庫段で loogle 十数クエリ、実装段で 0-hit 1 件） |
| 見積との差 | 下振れ（200–400 → 242） | 上振れ（250–500 → 594） |
| 結論 | どちらも**行数見積は着地の可否を予言しなかった** | 同左 |

---

## 2. 数学的方針

### (1) 構造恒等式で K を払う

この機械の受理 program は必ず `selfDelimit d`（単進長さ前置 + payload）の形をしていて、
`|selfDelimit d| = 2·|d| + 1`。したがって「最短 payload 長」`payloadComplexity x` を新たに定義すると

```
prefixComplexity x = 2 * payloadComplexity x + 1
```

が **不等式ではなく恒等式**として成り立つ（`Levin.lean:114`）。両辺 `le_antisymm` で 15 行。

### (2) 数え上げで P_U の上界を出す

`x` を出力する program 全体は「長さ ≥ m(x) の payload」へ単射に入る（`selfDelimit_parseUnary_snd_of_mem` で
program からその payload を取り出す写像が単射になる）。その像の重み `2^{-(2|d|+1)}` を
`2^{-m(x)} × 2^{-|padDelimit m d|}` に分解し、後半に Kraft を **順向きに**当てる。ここで
`padDelimit m d = replicate (|d| - m) true ++ false :: d` は、単進前置を `m` だけ短くした「機械の program ではない」
符号語で、必要なのは像の prefix-free 性だけ。結果 `P_U(x) ≤ 2^{-m(x)}`（`Levin.lean:190`）。

### (3) 対数化

(1)(2) を合わせて `K(x) = 2m(x) + 1 ≤ 2·(-log₂ P_U(x)) + 1`。

**時間的構造**: (1) の恒等式に気づいた時点で (2)(3) は一直線だった。逆に言えば、
**この leg の価値の大半は (1) を「障害」ではなく「定理の形の決定要因」として読み直したこと**にある（§4.1）。

---

## 3. Mathlib 補題探索の実録

**この leg で打った loogle クエリは 1 本だけ**（存在確認であって探索ではない）。

| 必要だったもの | クエリ | 結果 |
|---|---|---|
| 単射に沿った tsum 比較 | `loogle "ENNReal.tsum_comp_le_tsum_of_injective"` | 存在。`Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean:250`、既存 import 鎖で到達可能 |

残りは `rg` で in-tree を見るだけで足りた。使った Mathlib 補題（キーステップのみ）:
`kraft_mcmillan_inequality` / `ENNReal.tsum_eq_iSup_sum` / `Finset.sum_image` / `ENNReal.ofReal_sum_of_nonneg` /
`ENNReal.tsum_mul_left` / `Real.logb_le_logb_of_le` / `Real.logb_pow` / `Real.logb_inv` / `ENNReal.toReal_mono`。
対数ステップは兄弟ファイル `UniversalProbability.lean:54` の写経で済んでいる。

**「無かった」もの**:

- **`selfDelimit_length`（in-tree に不在）** — `rg -n "selfDelimit" InformationTheory/` で家系全体を見て、
  長さを計算しているのは `prefixInterpretProg_length` が `simp only [selfDelimit, …]` で inline に潰している 1 箇所だけ、
  と判明。`|selfDelimit bs| = 2·|bs| + 1` は P8 の全ステップで使うので `PrefixMachine.lean` に 3 行で追加した。
  **教訓**: 「機械の定義の最も基本的な数量」が家系に無いまま 4 ファイル進んでいた。
  在庫エージェントは Mathlib 側の不在は列挙するが、**in-tree 側の「あるはずの基本補題の不在」は列挙しない**。
- **`mul_le_mul_left'` が deprecated** — 置換先は `mul_le_mul_right`。
  `Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:74` の alias で確認。
  **接尾辞 `right` の方が左から掛ける**ので、名前だけ見て選ぶと逆を掴む。

---

## 4. 試行錯誤と後戻り

### 4.1 「SFE 逆向き構成 200–400 行」という見積が、数え上げで丸ごと消えた

**状況**: 計画の証明戦略欄は「`P_U(x)` の質量から長さ `≈ -log₂ P_U(x)` の prefix program を
Shannon-Fano-Elias（算術符号）で**逆向きに構成**する。Kraft は符号の存在の必要条件を与えるだけなので、
実際の構成は self-build」と書いていた。第 2 波最大の山と位置づけられていた部分。

**原因**: 「Kraft の逆向き（重みの列から符号を作る）が要る」という見立ては、**加法版を狙う限りは正しい**。
factor-2 版でよければ、必要なのは「program 集合の重みの上界」だけであり、これは Kraft を順向きに当てて出る。
つまり構成が要るかどうかは、**証明したい命題の係数**が決めていた。

**抜け方**: program を payload へ単射で送り、`padDelimit` で再ラップした像に Kraft を順向きに適用（§2(2)）。
SFE 符号器は 1 行も書いていない。

**教訓**: 見積の単位を「工程（逆向き構成が要る／要らない）」ではなく「命題（どの係数の主張を狙うか）」に置く。
計画テンプレートの「証明戦略」欄が工程だけを書かせる形になっていると、命題が揺れたときに見積が丸ごと無効になる。
**着手前ゲートで先に確定すべきは行数ではなく命題**。

### 4.2 恒等式が「加法版への出口」を機械的に閉じた

**状況**: 計画は着手前に 3 択のゲートを置いていた。(i) 自己限定済み記述を渡して加法定数に落とす（実装者の第一候補）/
(ii) 機械の定義を変える（ripple 21 decl / 3 file）/ (iii) factor-2 版へ言い換える。

**原因**: (i) が可能かどうかは、`prefixComplexity` が payload 長にどれだけ強く縛られているかで決まる。
受理 program が `Set.range selfDelimit` に閉じているため、`K(x) = 2·m(x) + 1` は**恒等式**であって
「今の証明が緩いだけ」ではない。記述の符号化をどう変えても `K` は `2·(何か) + 1` の形にしかならず、
**加法定数は原理的に回復しない**。

**抜け方**: (iii) を採り、factor-2 版を「言い換え」ではなく「実在する機械に対する真の両側 bound」として証明した。
加法版は教科書の「加法的普遍 prefix 機械」に関する主張であり、この機械では真偽未確定として plan 側に park。

**教訓**: **恒等式チェックは着手前ゲートに置くべき最も安い判定**だった。
`prefixComplexity x = 2 * payloadComplexity x + 1` は 15 行で証明できる。これを 1 本先に通していれば、
(i) が第一候補になることも、200–400 行の見積が立つこともなかった。
一般化すると「複雑さ量 `C` と、その下位の量 `c` の関係が `=` か `≤` か」を先に決めよ、という規則になる。
`≤` なら証明の緩さの余地があるが、`=` なら**その係数は定理の形の一部**であって、いくら工夫しても消えない。

### 4.3 `padDelimit` の像を prefix-free にするには定義域制限が要る

**状況**: `padDelimit m` の像に Kraft を当てたい。素直には `Set.range (padDelimit m)` に当てたくなる。

**原因**: `m = 1` のとき `padDelimit 1 [] = [false]` は `padDelimit 1 [x] = [false, x]` の接頭辞。
**無制限の range は prefix-free ではない**（実装時に反例を確認した）。

**抜け方**: 集合を `padDelimit m '' {d | m ≤ d.length}` に制限した。prefix-free 性の証明は、
2 つの符号語の**両方**について `m ≤ |d|` を使う（`Levin.lean:147`、`Set.mem_setOf_eq` を展開してから `omega`）。
`padDelimit_length` も同じ制限が要る（ℕ の切り捨て減算のため）。

**教訓**: 「重み計算の都合で置いた制限」に見えるものが、実は**集合が prefix-free であるための本質的条件**だった。
副条件を「あとで効くかもしれない regularity」として惰性で付けるのではなく、
どの補題がその副条件を本当に消費するかを 1 回確かめると、署名を後から締め直す手間が消える。

### 4.4 撤退出口 `sorry + @residual` が使えない命題があった

**状況**: 計画の撤退ライン R-W2b は「P8 が発散したら加法版を `sorry + @residual(plan:kolmogorov-w2-levin)` として置き、
第 2 波を最小成果で締める」と定めていた。honesty ゲートがこの出口自体を却下した。

**原因**: `@residual` を貼るには**命題を Lean に書く**必要がある。加法版はこの機械に対して
「未証明」ではなく**真偽不明**（偽の公算もある）なので、署名として書いた時点で
「偽かもしれない含意を主張する」= tier 5 `false-statement` を自作することになる。
`@audit:defect(false-statement)` も使えない（この用法は機械検証可能な偽性、つまり反例か refutation 補題の in-tree 存在を前提とする）。

**抜け方**: コード側には何も置かず、module docstring の Implementation notes に
「何を主張していないか + なぜ（加法的普遍性がこの機械に無いから）」を書いた。park は plan 側の slug のみ。

**教訓**: プロジェクトの honesty 階層は「最も正直なのは `sorry`」としているが、
**これは命題が真であることを暗黙の前提にしている**。真偽不明の命題に対しては `sorry` すら置けず、
正しい置き場は散文（docstring）＋ plan 側 slug になる。撤退ラインを設計する段で
「その撤退先の命題は真だと分かっているか」を 1 回問う欄が要る。

### 4.5 一般化リファクタが `@audit:ok` を無検査で運んだ

**状況**: Kraft の無限版を「この機械の受理集合」から「任意の prefix-free 集合」へ一般化した。
旧名 `tsum_inv_two_pow_length_le_one` は**署名を byte 単位で不変**に保ち、body だけ一般版への委譲に置き換えた
（consumer 2 件 = `chaitinOmega_le_one`（`Omega.lean:49`）/ `universalProb_le_one`（`UniversalProbability.lean:45`）は無変更でコンパイル）。

**原因**: 一般版 `PrefixFree.tsum_inv_two_pow_length_le_one` は旧宣言の docstring をそのまま引き継いだため、
docstring 末尾の `@audit:ok` も一緒に移動した。grep 上は「監査済」に見えるが、
**一般化後の署名は誰も見ていない**状態だった（honesty ゲートが独立検証して事後的に裏付けた）。

**教訓**: 「docstring ごと一般版へ移し、旧名を wrapper として再作成する」リファクタは、
監査タグの搬送経路になる。タグは署名に紐づくので、署名が変わる移送では**タグだけ落として再監査に回す**のが正しい。
`git diff` ベースの機械的な検出が可能（docstring 内の `@audit:ok` が、署名が変わった宣言へ移動した diff を検出する）。

### 4.6 stale olean の phantom

`PrefixMachine.lean` に `selfDelimit_length` を足した直後、`Levin.lean` 側が `unknown identifier` を出した。
`lake build InformationTheory.Shannon.Kolmogorov.UniversalProbability` 1 回で解消。
CLAUDE.md に既知として書かれている現象で、コストは 1 コマンド。

---

## 5. ボトルネックではなかったもの

- **Mathlib 補題探索** — loogle 1 回。必要な補題は在庫と兄弟ファイルで既に名指しされていた。
  この family は「Mathlib の在庫が薄い」のではなく「在庫調査が既に済んでいた」。
- **タクティク選択** — `omega` / `simp only` / `calc` でほぼ片付いた。`ENNReal` の計算も兄弟ファイルの写経。
- **skeleton から埋めるループ** — dead end 無し。方針の書き直しに至った `sorry` は 1 本も無い。
- **consumer への ripple** — Kraft を一般化したが、旧名を署名同一の wrapper として残したので consumer 側の編集は 0。
  「一般化＋旧名 wrapper」は ripple を 0 にする定石として機能した（ただし §4.5 の副作用付き）。
- **撤退ライン R-W2b（400 行超で発散）** — 発動せず。

---

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたであろうコスト |
|---|---|---|
| 高 | **着手前「恒等式ゲート」**: 主対象の複雑さ量と、その下位量の関係が `=` か `≤` かを 1 本の補題で先に確定させる（§4.2） | 計画段階の 3 択ゲートのうち第一候補が原理的に不可能だと即断できた。見積 200–400 行の根拠だった工程が丸ごと消える判断が、15 行の補題で先に取れる |
| 高 | **命題単位の見積テンプレート**: 「証明戦略」欄より前に「狙う命題の係数」欄を置き、係数が変わったら見積を無効化する（§4.1） | 第 2 波最大の山という位置づけ自体が、狙う係数に依存していた |
| 中 | **in-tree 基本補題の不在検出**: 家系の中心 def（ここでは `selfDelimit`）について、長さ・単射性など基本量の補題が in-tree に無いことを列挙する（§3） | 在庫エージェントは Mathlib 側の不在しか出さない。in-tree 側の不在は実装中に発見される |
| 中 | **監査タグ搬送の検出**: docstring 内の `@audit:ok` が、署名の変わった宣言へ diff 上で移動したときに警告（§4.5） | 「grep 上は監査済だが実際は未監査」の状態を機械的に潰せる |
| 低 | **deprecated alias の方向表示**: `mul_le_mul_left'` → `mul_le_mul_right` のように、接尾辞と実際の作用方向が逆になる置換の警告（§3） | 1 回の試行 |

---

## 7. 補足

### 打った loogle コマンド（全量）

```bash
./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index \
  "ENNReal.tsum_comp_le_tsum_of_injective"
```

### 着手前に通しておくべきだった 1 本（§4.2 の恒等式ゲート）

```lean
theorem prefixComplexity_eq_two_mul_payloadComplexity_add_one (x : ℕ) :
    prefixComplexity x = 2 * payloadComplexity x + 1
```

`le_antisymm` の 2 方向とも、`payloadComplexity_spec`（sInf 到達性）と
`dom_imp_mem_range`（受理 program は `selfDelimit` の像）から直接出る。
この 1 本が通った時点で「加法版はこの機械では取れない」が確定する。

### 採らなかった代替案

- **機械の定義を変えて加法的普遍 prefix 機械を建てる**（計画の出口 (ii)）。
  任意の `Nat.Partrec.Code` 上で dovetail 先着順フィルタを回す必要があり、leg ではなく別 moonshot 級。
  ripple は実測済（`prefixUniversalEval` の direct consumer 21 decl / 3 file、加えて `chaitinOmega` の値が変わるため
  P9 の着地物の再証明が要る）。
- **factor-2 版を「Levin 符号化定理」と命名する**。name laundering に当たるため禁止のまま維持。
  headline 名 `prefixComplexity_le_two_mul_neg_logb_universalProb` は係数 2 を名前に含んでいる。

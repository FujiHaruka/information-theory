# N8 — 敵対的独立監査 (判定枠 3 段 1 組の第 3 段 = 層 3 へ載せる)

> **Parent**: [`bc-open-problem-t3c-plan.md`](bc-open-problem-t3c-plan.md) §4.6 (敵対的独立監査) / §3.1 (禁止される書き方)。
> **対象 commit**: `51d1ccb1` (起票は `c90baafb`)。
> **対象ファイル**: `InformationTheory/Shannon/BroadcastChannel/OuterBoundTransport.lean` の
> 新規 6 宣言 (`/-! ### A directional combination of the plain right-hand sides -/` 節)。
> **散文側の出典**: [`bc-t3c-n7-shoulder-certificate.md`](bc-t3c-n7-shoulder-certificate.md) §2.1 の `(R1)`。
> ⚠ **監査者は実装に関与していない**。⚠ **既定の立場を「主張は誇張されている」に置いた**。

## 0. 総合判定

**訂正あり生存。** 主張の本体 3 つ — (i) `t ≤ 1` を落とせる / (ii) マルコフ性なしで立つ /
(iii) 載ったものは `(18b)`/`(18i)` の右辺と字面一致する — は **3 つとも生存**した。
⚠ **訂正 2 件は散文 (docstring) の読ませ方**であり、**Lean の命題は 1 つも覆っていない**。

⚠⚠ **本 leg が載せたのは `(R1)` の 1 本だけ**であって「N7 §2.1 の上界の連鎖」全体ではない
(`(R2)` / `(R3)` は載っていない)。⚠ **台帳に書くときは「連鎖」と書かない**。

## 1. 論点 1 — `t ≤ 1` を落としたのは正当か (⚠ 結論を曖昧にしない)

**正当。命題は `t ≥ 0` 全体で真である。** 監査者が証明本体を読まずに定義だけから代数を組み直し、
機械で確認した (下記 R2)。`M := min{I(W;Y), I(W;Z)}`, `a := I(U;Y|W)`, `c := I(X;Z|W,U)` と置くと

```
plainDirectionalBound − plainDirectionalCombination
  = (I(W;Y) − M) + t·( (a + c) − min{第1枝, a + c} )
```

で、`t` の係数は `M` の側で完全に相殺する (`(1−t)M + tM = M`) ⟹ 残る 2 項はどちらも非負、
`t ≥ 0` だけで十分。⚠ **`t > 1` で `(1−t) < 0` になることは不等式の真偽に効かない** — 効くのは
`t < 0` の側だけである (R1 で反例を機械確認)。

**(b) 幾何的な読みの点では docstring に訂正が要る。** `(1−t)·(18b) + t·(18i)` を
**方向 `(0,1,t)` の支持値の上界**として読む LP の読みは、**重みが 2 つとも非負** = `t ∈ [0,1]`
でしか成り立たない (`t > 1` では負の重みで制約を足すことになり、何も上から抑えない)。
⟹ 現在の docstring は「方向 `(0,1,t)` が作る組合せ」+「任意の非負 `t` で」を **同じ文**に置いており、
**LP の読みが `t ≥ 0` 全体へ延びるかのように読める**。⚠ **これは §3.1 が禁じる「レート領域について
何か言ったかのように読める書き方」に触れる** ⟹ 訂正 (§4 の C1 / C2)。

## 2. 論点 2 — 載せた命題は `(R1)` と同じか、弱いか (⚠ 結論を曖昧にしない)

**同じか、むしろ強い。弱くはない。** N7 §2.1 の逐語と Lean の def を 1 項ずつ照合した:

| 散文 (`bc-t3c-n7-shoulder-certificate.md` §2.1) | Lean | 判定 |
|---|---|---|
| `(18b) = min{I(W;Y), I(W;Z)} + I(U;Y\|W)` | `plainFirstUserBound` (L871) | **字面一致** |
| `(18i) = min{I(W;Y), I(W;Z)} + min{ I(V;Z\|W)+I(X;Y\|V,W), I(U;Y\|W)+I(X;Z\|U,W) }` | `plainSumRateBound` (L565) | **字面一致** (条件付けの対の順序のみ後述) |
| `(R1)` 右辺 `I(U,W;Y) + t·I(X;Z\|U,W)` | `plainDirectionalBound` (L955) | **字面一致** (同上) |

**条件付けの対の順序は意味の違いではない。** 散文は `(V,W)` / `(U,W)` / `(U,W;Y)` の順、Lean は
`(W,V)` / `(W,U)` / `(W,U;Y)` の順。⚠ **これは M17 の設計上の分岐として既に台帳に記録済**
(`bc-facts.md` `## M17 (T3b)` の M17-d、「連鎖律の結論形が条件付け側を先に出すため」)。
移送補題は **2 本とも in-project に実在** (機械確認): `condMutualInfo_map_cond_measurableEquiv`
(`CondMutualInfo.lean:535`) / `mutualInfo_map_left_measurableEquiv` (`MIChainRule.lean:35`)。
⟹ **命題の強さは変わらない**。

**強くなっている 2 点**: (a) 散文は `t ∈ [0,1]`、Lean は `0 ≤ t` / (b) 散文の (R1) は
`(U,V,W) −− X −− (Y,Z)` を場に置いた上での主張だが、**Lean の `plainDirectionalCombination_le_plainDirectionalBound`
はマルコフ仮説を 1 本も持たない**。⚠ **どちらも「弱いものを載せた」の逆**である。

⚠ **射程の限定 (縮んでいないが明記する)**: 載ったのは `(R1)` **のみ**。`(R2)` (`U' := (U,W)` の
事後分解) と `(R3)` (2 つの緩和) は載っていない。⟹ **`h_Thm7(0,1,t)` の上界そのものは Lean に無い**。

## 3. 論点 3 — `plainFirstUserBound` / `plainSumRateBound` の出自の齟齬 (⚠ 結論を曖昧にしない)

**齟齬は存在しない。ブリーフの前提が事実として誤っている。** `git log -S` で機械確認した:

```
plainSumRateBound     → 1170bbe0 (M17)   -- M16 ではない
plainFirstUserBound   → 78af2268 (M18)   -- M16 ではない
ファイル自体の新規作成 → 14217cbf (M16)
```

⟹ **M16 が入れたのはファイルであって、この 2 つの def ではない**。台帳の `(31a)`–`(31e)` の帰属は
M16 の **別の 5 定理** (`singleAux*_le_twoAux*`) に付いており、N8 はそれらに 1 本も触れていない。
**この 2 def の帰属は M17 / M18 の台帳側に既にあり、そこでの番号は `(18h)`/`(18i)` と
`(18a)`–`(18g)` = いずれも Theorem 7 の番号**である (`bc-facts.md` の M17-b / M18-e)
⟹ **N7 / N8 が引く `(18b)`/`(18i)` と同じ定理を指している**。

⚠ **監査の射程の限定 1 つ**: 本監査が照合した逐語は **N7 証明書 §2.1 が引用した文字列**であって、
`$LIT/auxrec.txt` そのものではない (本監査の環境に当該ファイルが無い)。⟹ **「Lean の def が
`(18b)`/`(18i)` の字面と一致する」までが本監査の裏取り**であり、**その字面が auxrec の当該行である
ことは N7 証明書 + M17/M18 台帳の記録に依存する**。⚠ **成果物で番号の帰属を新たに主張するなら、
この 1 段は別に裏を取ること**。現時点で `51d1ccb1` はコードにも plan にも番号の帰属を書いていない
(plan §5 の「M16 が…載せた同じ器」は**ファイルの帰属**であり正しい) ⟹ **指摘事項なし**。

## 4. 論点 4 — `hmarkov` は precondition か load-bearing か

**precondition。DEFECT ではない。** 3 つの根拠:

1. **核の再構成テスト**: `hmarkov` (+ 可測性) を全部認めても、**結論の不等式は手に入らない**。
   実際、不等式の本体 `plainDirectionalCombination_le_plainDirectionalBound` は
   **`hmarkov` を引数に取らない**。`hmarkov` が使われるのは `plainDirectionalBound` と
   `plainDirectionalBoundCondFree` を**繋ぐ等式 1 本**だけで、そこで消費されるのは既存の
   `mutualInfoReal_add_condMutualInfoReal_eq_of_markov` (L230) = 連鎖律 + `I((W,U);Z|X) = 0`。
2. **既存の比較対象と同型**: L604 の `hplain : IsMarkovChain μ (w,u,v) x (y,z,j)` と**同じ性格**で、
   新 `hmarkov` は **その特殊化 = より弱い**仮説 (`(W,U) ⊥ Z | X` のみ)。⚠ M16 の独立監査は
   `IsMarkovChain` を precondition と判定済 (`bc-facts.md` M16-c) ⟹ a fortiori。
3. **飾りでもない** (逆向きの確認): `hmarkov` を落とすと等式は偽になる (下記 R3)
   ⟹ 署名から落とせる仮説ではない。**「核を担う」と「不要」の間の precondition** である。

## 5. 論点 5 — CORE の定型 tell

| tell | 判定 |
|---|---|
| 循環 (仮説型 ≡ 結論型、`:= h`) | **なし**。仮説は可測性 / `0 ≤ t` / `IsMarkovChain` のみで、どれも結論型ではない |
| `:True` スロット | **なし** |
| 退化定義の悪用 | **なし**。`t < 0` で偽 (R1) ⟹ 恒真ではない |
| name laundering | **なし**。`_le_` / `_eq_condFree` は主張どおり。`_unconditional` / `_full` / `_discharged` を使っていない |
| under-hypothesized | **なし**。定義だけから独立に再導出して機械確認 (R2) |
| **def が結論を先取りしていないか** | **していない**。3 つの def はいずれも `ℝ` の**式**であって `Prop` ではなく、`plainDirectionalBound` は「combination を抑える値」ではなく `I(W,U;Y) + t·I(X;Z\|W,U)` という**明示の情報量式**として定義されている。⟹ 不等式は定義の展開では出ず、`min` の枝落としと連鎖律が要る |

## 6. 論点 6 — 誇張の検出

**禁止語形は 1 つも出ていない。** `Thm7 ⊄ Thm8` / 「方法の死」を「包含の否定」と書く / `R ∈ Thm7` /
「あと少し」「残るのは行数と配線だけ」/「§0 に近づいた」— **全て不検出**。
2 本の不等式定理には逐語の免責が入っている (「This relates right-hand sides of constraints to one
another, and says nothing about the rate regions those constraints cut out.」)。
module docstring も L55-57 で同じ免責を持つ。

⚠ **ただし 2 件の訂正**: 下記 C1 / C2 は、**領域について何か言ったかのように読める線**に触れている。

### 訂正一覧

| # | 箇所 | 現状 | あるべき形 |
|---|---|---|---|
| **C1** | `OuterBoundTransport.lean:965` (`plainDirectionalCombination_le_plainDirectionalBound` の docstring 1 文目) と `:1017` (`…_le_plainDirectionalBoundCondFree` の同) | 「The combination **the direction `(0, 1, t)` forms** from the two plain right-hand sides is at most … **for every nonnegative `t`**」 | 範囲を述べる文から方向の帰属を外す。例: 「The combination `(1 - t) · plainFirstUserBound + t · plainSumRateBound` is at most … for every nonnegative `t`」。⚠ **免責の文はそのまま残す** |
| **C2** | 同ファイル module docstring `:113-114` (`## Main statements`) | 「**every nonnegative weighting** of the two plain right-hand sides is at most …」 | 「the weighting at **every `t ≥ 0`**」。⚠ **`t > 1` では `(1−t) < 0` なので "nonnegative weighting" は字義的に誤り** |
| **C3** (任意) | 同 `:945-947` (`plainDirectionalCombination` の docstring) | 方向 `(0,1,t)` が「pairs」すると述べる (範囲の主張は無い) | 重みが 2 つとも非負なのは `0 ≤ t ≤ 1` に限る旨を 1 節足すと C1 の再発を防げる |
| **C4** | 台帳 `bc-facts.md` の N8 節 (**未作成**) / commit message | commit `51d1ccb1` の件名は「上界の**連鎖**を層 3 へ」 | **載ったのは `(R1)` の 1 本だけ** ⟹ 台帳では「連鎖」と書かず `(R1)` と名指す (`(R2)`/`(R3)` は載っていない) |

⚠ **C1–C3 は散文のみ**であり、**Lean の命題・署名・証明は 1 文字も変えない**。

## 7. 反証試行 — **5 本試して 2 本が成立、3 本が落ちた**

| # | 標的 | 結果 |
|---|---|---|
| **R1** | 「`0 ≤ t` は飾りで、命題は全 `t` で真」 | ⭐ **反証成立** (`t = −1`, `I(W;Y)=I(W;Z)=a=第1枝=0`, `c=1` で偽)。⟹ `ht` は本物の precondition。実現例もある (`W`/`U`/`V` 定数、`X = Z` 一様ビット、`Y` 定数) |
| **R2** | 「`t ≤ 1` を落としたのは誤りで、`t > 1` に反例がある」 | **反証は落ちた** — 定義だけから組み直した骨格が `0 ≤ t` 全体で機械証明できた ⟹ 落としたのは正当 |
| **R3** | 「`hmarkov` は飾りで、等式は無条件に立つ」 | ⭐ **反証成立** (`t=1, c=0, I(X;Z)=0, I(W,U;Z)=1` で偽)。実現例: `X` 定数・`Z = U` 一様ビット・`W` 定数 ⟹ `hmarkov` は落とせない |
| **R4** | 「def が結論を先取りしており、不等式は展開だけで出る」 | **反証は落ちた** — `plainDirectionalBound` は明示の情報量式で、`min` の枝落とし + 連鎖律が要る |
| **R5** | 「`plainFirstUserBound`/`plainSumRateBound` は M16 由来で `(31a)`–`(31e)` に属し、`(18b)`/`(18i)` への帰属は裏が無い」 | **反証は落ちた** — `git log -S` で M17 / M18 由来と確定、台帳の番号も `(18*)` 系 (§3) |

⚠ **R2 / R4 / R5 は「潰しにいって潰せなかった」**であり、追認ではない。

## 8. 実行した検証コマンドと出力

```
$ lake env lean InformationTheory/Shannon/BroadcastChannel/OuterBoundTransport.lean
(出力 0 バイト、exit 0)                                    # タグ書込の前後で 2 回

$ lake env lean <対象ファイルの複製 + #print axioms 6 行>
'…plainDirectionalCombination_le_plainDirectionalBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'…plainDirectionalBound_eq_condFree'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'…plainDirectionalCombination_le_plainDirectionalBoundCondFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'…plainDirectionalCombination' / '…plainDirectionalBound' / '…plainDirectionalBoundCondFree' も同じ 3 公理
```

⚠ **`sorryAx`-free は必要条件にすぎない** ⟹ **署名走査を併せた**: 6 宣言の仮説は
`[IsProbabilityMeasure μ]` / `[IsFiniteMeasure μ]` (instance) / `Measurable *` (regularity) /
`0 ≤ t` (§7 R1 で必要性を確認) / `IsMarkovChain` (§4 で precondition と判定) の **5 種のみ**。
⟹ **load-bearing hypothesis なし**。

```
$ rg -c 'sorry|@residual' InformationTheory/Shannon/BroadcastChannel/OuterBoundTransport.lean
0                                                          # @residual は元から 0 本、1 文字も触っていない

$ rg -n '@audit:suspect|@audit:staged|@audit:defer|🟢ʰ|NOT a discharge' <同ファイル>
(0 件)                                                     # deprecated タグの残置なし
```

**独立な代数の組み直し** (証明本体を読まず、定義だけから骨格を作って機械検証。R1–R3 の反例も同じ場所):

```lean
example (IWY IWZ a b1 c t : ℝ) (ht : 0 ≤ t) :
    (1-t)*(min IWY IWZ + a) + t*(min IWY IWZ + min b1 (a+c)) ≤ (IWY + a) + t*c := by
  have h1 : min IWY IWZ ≤ IWY := min_le_left _ _
  have h2 : min b1 (a+c) ≤ a + c := min_le_right _ _
  nlinarith [mul_le_mul_of_nonneg_left h2 ht]
```

(`lake env lean` が 4 本の probe すべてを通した。exit 0)

## 9. 書き込んだタグ (コード側が SoT)

| 宣言 | tag | 理由 |
|---|---|---|
| `plainDirectionalCombination` (L945) | **`@audit:ok`** | 定義は式のみ。docstring に範囲の主張が無い (C3 は任意) |
| `plainDirectionalBound` (L953) | **`@audit:ok`** | |
| `plainDirectionalBoundCondFree` (L986) | **`@audit:ok`** | |
| `plainDirectionalBound_eq_condFree` (L994) | **`@audit:ok`** | §4 で precondition 判定、方向の言及なし |
| `plainDirectionalCombination_le_plainDirectionalBound` | ⚠ **保留** | 命題は honest だが docstring が C1 に触れる。⚠ **語彙に「散文の留保つき pass」が無いので新語を作らず保留にした** |
| `plainDirectionalCombination_le_plainDirectionalBoundCondFree` | ⚠ **保留** | 同上 |

**保留 2 本の closure 条件**: **C1 を当てたら `@audit:ok` を付けてよい** (Lean 側の再監査は不要 —
命題・署名・証明は本監査で機械検証済)。⚠ **`@residual` タグは 1 文字も触っていない** (元から 0 本)。

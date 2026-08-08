# A2 novelty gate (N13) — 計算可能解析の (β) 語彙の新規性判定

**判定 = `redundant`**

**親** [`bc-open-problem-t3c-plan.md`](bc-open-problem-t3c-plan.md) §5.3 アーク宣言 (A2) 反証条件 (1)。
判定対象は **(β) 語彙 5 項目を集合水準の def 群として層 3 へ置くことの新規性だけ**。既定の立場
`redundant` を成立させにいき、**成立した** — 潰れた命題は §1 に 7/7 で挙げ、**潰れなかった部分は 0** である。
⚠ **`redundant` は「この層は要らない」ではない** — 既知の散文経路 (`## L2 (T3)` 行 6) を Lean で閉じる
なら中核 1–7 は要る (子 plan 単位 A)。要らないと判定したのは**新しい対象としての地位**だけである。
⚠ 再現本数 (`inert` 判定) は N15 の担当で本 gate は判定しない。⚠ 数値と逐語の SoT は `bc-facts.md`。

## 0. 定義の補修 (⚠ アーク宣言のまま採用してはならない)

**(0-a) ⚠⚠ 5 項目のうち 3 項目は「定義」ではなく「定理の言明」である** (`machine`)。言明の受け皿
`docs/shannon/probes/t3c-n2/r2-effectivity-layer.lean` は現時点でも通る (再検証
`lake env lean docs/shannon/probes/t3c-n2/r2-effectivity-layer.lean` = **EXIT=0** /
`scripts/sig_view.ts --names <同 file>` = **20 decls, 0 with sorry**)。内訳は **真の def 9 本 /
`Prop` 値の定理言明 7 本 (`LExists` `LForall` `Pi01ClosedUnderIInterUniform` `Pi01ClosedUnderIInter`
`ConstraintSetPi01` `WitnessEffectivelyCompact` `MutualInfoEffectivelyContinuous`) / 証明つき古典定理
3 本**。後者 7 本は N2 §3.2 の**中核 1–4・6–7 そのもの**を `def _ : Prop` に駐車したものである。
**補修**: 層 3 へ移すときは `theorem … := by sorry` + `@residual(plan:bc-computable-region-formalization)`
の形で置く。⚠⚠ **`def _ : Prop` のまま置き、下流が `(h : LExists n m)` を仮説に取った瞬間に
CLAUDE.md の load-bearing hypothesis bundling (tier 5) になる**。⚠ **現存の defect ではない** —
probe は `docs/` 配下で `InformationTheory/` からは 1 行も参照されていない。禁じるのは**既定値としての形**である。

**(0-b) 落ちている依存 1 — `Primcodable ℚ`** (`machine`、SoT = `## N2 (T3c)` N2-h)。
`import Mathlib.Data.Rat.Denumerable` が要り、**`import InformationTheory` の閉包に入っていない**。

**(0-c) ⭐ 落ちている依存 2 — 座標づけの def が 2 本まるごと無い (本 gate の新規発見)**。(β) 層の周囲空間は
`Set (Fin n → ℝ)`、witness 空間は `simplexN n` (r2:89)。一方 3 レート領域層 (単位 B、
`probes/t3c-n2/r1-thm7-region.lean`) の witness は `Measure (Amb …)` / `ProbabilityMeasure α` /
`Kernel …` で、レート領域は `Set (ℝ × ℝ × ℝ)`、スロットは `.toReal` 済 (`machine`:
`rg -n 'Measure|toReal|Set \(ℝ' docs/shannon/probes/t3c-n2/r1-thm7-region.lean`) ⟹ **中核 3
(`IsEffectivelyCompactN (simplexN n)`) は r1 の witness 空間に当たらない**。要るのは
「有限型上の測度 ↔ 単体」と「`ℝ × ℝ × ℝ` ↔ `Fin 3 → ℝ`」の 2 本で、**アーク宣言の 5 項目にも r2 にも無い**。
⚠ 既製の橋は出てこない (`loogle-neg`: `stdSimplex, MeasureTheory.Measure` / `MeasureTheory.ProbabilityMeasure, stdSimplex`
がいずれも `Found 0 declarations`。⚠ **0 件は必要条件どまり**)。

**(0-d) 添字衝突**: r2 の `n` は**周囲空間の次元**、`## L2 (T3)` 行 6 の `𝒯_k` の `k` は **`|J| ≤ k`**、
N2 の `kv : AuxIdx → ℕ` は**補助変数ごとの基数**。3 つとも別物である。

## 1. 言明可能性テスト — **7 本中 7 本が潰れた。潰れなかった部分は 0 である** (`human-judgment`)

テストの形は A1 §1 と同じ: 台帳が現在この機構について述べている命題が、**(β) 語彙なしの既存語彙
(Mathlib の `REPred` / `Primcodable` + 有理球 2 行 + 古典 `IsCompact`) へ逆向きにも損失なく翻訳できるか**。

| # | 台帳の命題 | (β) 語彙なしの形 | 判定 |
|---|---|---|---|
| 1 | `## L2 (T3)` 行 5 (P1) | 「補集合を一様に枚挙する `REPred` が在れば、⋂ の補集合を枚挙する `REPred` が在る」 | **潰れた** |
| 2 | `## L2 (T3)` 行 6 (P2) | 「`Thm7(W)` はコンパクトで、`{(W の添字, 有理球の有限列) : 被覆}` が c.e.」 | **潰れた** |
| 3 | `## L2 (T3)` 行 10 (P4) | 同上を一階論理式の仮定つきで述べ直すだけ | **潰れた** |
| 4 | `## L0 (T3)` 行 3 (overt) | 「`{(W の添字, 有理球) : Marton(W) ∩ 球 ≠ ∅}` が c.e.」 | **潰れた** |
| 5 | `## L0 (T3)` 行 5 ([AH] Def 2.4) | 定義そのものゆえ定義条件へ展開して終わる | **潰れた** |
| 6 | `## L5 (T3)` 行 4・5 / `## N2 (T3c)` N2-b / N2-g / N2-j | in-project・Mathlib の在庫の話で (β) を 1 語も要しない | **潰れた** |
| 7 | `## N2 (T3c)` N2-d | 「`∀ S, IsCompact S → (IsCompact S ∧ REPred …)` は型検査を通るが偽」 | **潰れた** |

⭐ **潰れる理由は A1 と構造的に違う** — A1 の `κ` は**既存述語のブール結合では書けない数値不変量**
だったのに対し、(β) の 5 項目は**本体が既存語彙だけで書かれた略記**である (r2:29–49 の 5 本はいずれも
`REPred` + `ratBallNSet` の 1–3 行) ⟹ 略記は `rfl` で両向きに戻り **損失は定義上 0** である。

⚠ **`redundant` を成立させにいく過程で潰しに行った反論 3 本** (どれも成立しなかった):

- **反論 1「Mathlib にも in-project にも 0 件だから新しい」** ⟹ **不成立**。宣言の不在は台帳の claim ではない。
  ⚠⚠ **「標準定義の転記」を「新しい対象の導入」と書くのは name laundering** (CLAUDE.md、tier 5)。
- **反論 2「一様性 (`W` / 添字 `k`) は既存語彙で書けない」** ⟹ **不成立**。r2 自身が
  `Pi01ClosedUnderIInterUniform` を `E : ℕ × RatBallN n → Prop` + `REPred E` として**一様性を積添字に
  インライン**しており (r2:69–73)、(β) 語彙を 1 語も使わずに書けている。
- **反論 3「BC 側の集合水準という限定が新しい」** ⟹ **不成立、かつアーク宣言の誤り** — r2 に BC 由来の型は
  **1 つも無い** (`Fin n → ℝ` のみ)。子 plan §3.1 自身が単位 A を「**BC から独立**」と書いている (§7-2)。

## 2. in-repo 先行資産 — 近縁 1 本。⚠ 「1 段弱い」は**一般性の軸の話であって片側性の軸の話ではない**

- **結論形で走査した** (名前検索ではない、`machine`): `rg -n 'REPred|ComputablePred|Nat.Partrec|Partrec' InformationTheory/ --glob '*.lean'`
  ⟹ ヒットは**全件 `Kolmogorov/` の離散層**、**`REPred` は 0 件** (`rg -c 'REPred' … | wc -l` = `0`)。
  `rg -n 'Computable' InformationTheory/ --glob '*.lean' | rg 'Set |Metric|Topolog|IsCompact'` ⟹ **0 行**
  = **集合水準・位相つきの計算可能性述語は in-project に無い**。
- ⭐ **`IsComputableENNReal` を elaborate して署名で比べた** (`machine`、再検証 = スクラッチに
  `import InformationTheory` + `#check @InformationTheory.Kolmogorov.IsComputableENNReal` +
  `#print …` を書いて `lake env lean`)。出力逐語: `IsComputableENNReal : ENNReal → Prop` /
  `fun x => ∃ a, Computable a ∧ ∀ (n : ℕ), x ≤ ↑(a n) * 2⁻¹ ^ n + 2⁻¹ ^ n ∧ ↑(a n) * 2⁻¹ ^ n ≤ x + 2⁻¹ ^ n`
  ⟹ **引数は `ENNReal` 1 個、周囲空間もパラメータも位相も署名に無い** = N2-b の「点ごと・スカラー・位相 0 語」は
  署名で確認できた。消費者は **3 decl / 1 file** (`scripts/dep_consumers.sh InformationTheory.Kolmogorov.IsComputableENNReal`)。
- ⚠ **読みの訂正 1 件 (`human-judgment`)** — `## L5 (T3)` 行 4 の「標的との差は『スカラー ⟹ 平面集合』**1 段**」は
  **軸を 1 本に潰している**。`IsComputableENNReal` の本体は**上下 2 本の不等式 = 両側近似**であり、
  [AH] Definition 2.4-**3** (computable) の点版に当たる。実効コンパクト性は同 2.4-**1** = **片側**である ⟹
  **一般性の軸 (点 → 集合 / 無パラメータ → 一様 / 位相なし → 位相つき) では (β) が強いが、片側性の軸では
  `IsComputableENNReal` の方が強い条件を課している**。⚠ **「弱い方を 1 段持ち上げる」と読むと軸を取り違える**。
  ⚠ **この訂正は N2-b の判定 (強度 diff が §6-5 を支える) を動かさない** — 一般性の 3 点は署名で確認したとおりである。
  ⚠ **台帳への反映は N15 の担当であり、本 gate は facts を書き換えていない**。

## 3. 文献の先行 — ⚠⚠ **diff は「Lean の宣言として在るか」だけで、対象としての差は 0** (`human-judgment (primary)`)

取得 `curl -sL https://arxiv.org/pdf/2210.08309 -o /tmp/sct.pdf && pdftotext -layout /tmp/sct.pdf $LIT/sct.txt`
(⚠ **抽出テキストは public repo にコミットしない**。行番号は `pdftotext -layout` 出力に対する実測)。

- **実効コンパクト / computably overt / computable / Σ01 / Π01 = [AH] Definition 2.4 の 5 項目そのもの**
  (`sct.txt:230-248`)。
- **実効連続 = [AH] の「計算可能関数」の定義そのもの** — `sct.txt:227` 逐語: "f : X → Y is computable if the
  sets f −1 (BiY ) are effectively open, **uniformly in i**" ⟹ ⚠ **一様性まで込みで文献側にある**。
- **(L-∃) = [AH] Proposition 2.5 第 1 項** (`sct.txt:261-268`)。⚠⚠ **[AH] 自身が folklore と書いている** —
  `sct.txt:258-259` 逐語: "It is **a standard folklore result in computable analysis** that can drastically
  simplify many arguments. It can be found in [Pau16] for instance, but we include a proof for completeness."
- **⭐ 1 項目だけ [AH] に逐語が無い — overtness 版の (L-∀)**。[AH] の `overt` は**全 3 出現**
  (`grep -c -i overt $LIT/sct.txt` = **3**、= Definition 2.4-2 / 2.4-3 / `sct.txt:560`)、Proposition 2.5 第 2 項は
  **コンパクト側の双対** (`R` 実効開 + `Y` 実効コンパクト ⟹ `∀` が実効開、`sct.txt:270-274`) であって
  台帳 `## L2 (T3)` 行 6 が使う形 (`R` Π01 + `Y` overt ⟹ Π01) ではない。`sct.txt:560` 逐語:
  "computably overt set, **which will not be discussed in this paper**"。
  ⚠⚠ **これは `novel` を意味しない** — **(a)** 台帳が既にこの命題を持っており (`## L2 (T3)` 行 6 の
  「(L-∀) は**我々の証明**」) **アークが足すものではない**、**(b)** これは**定理**であってアークの型 (定義) の
  成果物ではない、**(c)** [Pau16] を読んでいないので **「文献に無い」とは言えない — 言えるのは「[AH] には無い」だけ**である。
- [Li21] / [N13] との差は台帳が既に持つ (`## L3 (T3)` 行 3 = exact decision と `ε` 近似の語義分離 /
  `## L0 (T3)` 行 1 = 脚注 1 の語義) ⟹ **アークはここにも 1 語も足さない**。

**⭐ diff 1 行**: 文献が既に持っているもの = **(β) 5 項目のうち 4 項目は [AH] Definition 2.4 の逐語、実効連続は
[AH] の計算可能関数の定義の逐語、(L-∃) は [AH] 自身が folklore と呼ぶ命題**。アークが足すと称するもの =
**それらの Lean 転記**。⟹ **対象としての差は 0 で、差は「Lean の宣言として存在するか」だけである**。

## 4. ⭐ 仕事をするかテスト — **3 点とも不成立** (⚠ A1 と同じ厳しさで測った)

**(4-a) 証明義務は 1 本も減らない** (`human-judgment`、裏づけは `machine`)。`## N2 (T3c)` N2-a より
中核 11 本は **0/11**、うち 1–7 が本層である。r2 は**その言明を型検査で通しただけ** (§0-a: 20 decls / 0 sorry /
証明つきは古典 3 本のみ) ⟹ **def を置いても証明義務は 0/7 のままである**。⚠ **「近づいた」と書かない**。

**(4-b) §0 の言明には要らない** (`machine` + `human-judgment`)。`## N2 (T3c)` N2-i: §0 の完了条件は
**肯定側・否定側とも実効性述語 0 個で言明できた** (55 行、`probes/t3c-n2/r4-goal-statement-discrete.lean`)。
⚠ 起票 (親 plan §5.1 の N13 ブロック) が選定理由に引いた「§0 の Lean 側はこの層を通らないと閉じない」は、
N2-i の逐語では**既知の散文経路 (`## L2 (T3)` 行 6) に対する必要性**であって §0 に対する必要性ではない —
**否定側 (親 plan §3 の T3-β) は 1–7 を 1 本も要求しない** (要るのは停止問題側の離散資産) ⟹ **起票の選定理由は
この限定を落としている** (§7-4)。

**(4-c) (C2) の残る穴に 1 文字も言わない** (`human-judgment`、A1 §4-d と同型)。`## L2 (T3)` 行 6 より
**`Thm7(W)` の一様実効コンパクト性は既に無条件の定理**であり、(C2) の残りは **`Thm7 = C` の厳密一致 1 点**
である (親 plan §1.1-ii)。(β) 語彙はその一致について何も述べない ⟹ **計算可能性側の主語は既に埋まっており、
語彙を置いても 1 mm も足さない**。

⚠ **3 点とも不成立であることは「この層が不要」ではない** — 不成立なのは **§0 への payoff** であって
**経路上の必要性**ではない (冒頭の射程の限定と同じ)。

## 5. 退化テスト — 構造の違う 2 例で殺せる (⚠ どちらも手構成であって数値掃引ではない)

⚠ 入力は `## N2 (T3c)` N2-d (「**型は実効性・一様性の脱落を守らない**」— 監査自身が
`∀ S, IsCompact S → IsEffectivelyCompactN S` を書き、**偽の命題をコンパイラが黙って通した**)。
⚠ **周囲空間は `[0,1]` に取る** (レート領域が有界閉方体に入るのと同じ設定)。

- **(D1) 実効性そのものの脱落** — `IsEffectivelyCompactN S := IsCompact S` と書いた退化形。
  **殺す witness = `S = {Ω}`** (`Ω` = Chaitin 定数の 1 点集合)。`{Ω}` はコンパクト。しかし 1 点集合が
  実効コンパクトなら、各 `n` について半径 `2^{-n}` の有理球 1 個からなる被覆が枚挙されるまで待てばよく、
  その中心が `Ω` の `2^{-n}` 近似を**両側で**与える ⟹ `Ω` は計算可能実数 ⟹ **in-repo の
  `chaitinOmega_not_computable` (`InformationTheory/Shannon/Kolmogorov/OmegaNoncomputable.lean:572`、
  `machine` = 上の §2 の `#check` 出力) に矛盾**する ⟹ 退化形は偽。
- **(D2) 一様性だけの脱落** — `Pi01ClosedUnderIInter` (r2:77。⚠ **これも型検査を通る**)。
  **殺す witness**: `|r_n − Ω| ≤ 2^{-n}` なる有理数列 `(r_n)` を取り `S_n := [r_n − 2^{-n}, r_n + 2^{-n}] ∩ [0,1]`。
  各 `S_n` は**有理端点の閉区間ゆえ個別には Π01** (補集合は有理球の決定可能な族)。しかし `⋂_n S_n = {Ω}` で、
  `[0,1]` の中で `{Ω}` が Π01 なら、`[q,1] ⊆ 補集合` の有限部分被覆をコンパクト性で探して `Ω < q` が
  半決定でき、同様に `q < Ω` も半決定できて `Ω` が計算可能になる ⟹ 同じ矛盾 ⟹ 非一様版は偽。
  ⚠ **族 `(r_n)` は計算可能でない** — それがまさに一様性の落ちている点である。
- ⚠ **2 例の構造は違う**: (D1) は**各成員の実効性**を落とす形、(D2) は**各成員は実効的なまま添字の一様性だけ**を
  落とす形である。⚠⚠ **どちらも `human-judgment`** — 導出は手構成で、Lean でも数値でも検証していない。
  ⚠ **使っているのは「実効コンパクト / Π01 ⟹ 計算可能点」の一方向だけ**である (逆向きは要らない)。

## 6. 再現の標的 (⚠ 「再現できた」ではない。N15 の再現本数テストの入力)

⚠ **反証条件 (1) が発火した以上、N15 が走るか否かは本 gate の決めることではない**。
⚠ **N5 較正 (b) を適用し、「facts 行のどの欄を再現するつもりか」を明記できないものは並べていない**。

1. **`## N2 (T3c)` N2-d の notes 欄** (「初版は `∀ S, IsCompact S → IsEffectivelyCompactN S` と書き、
   **これは偽の命題なのにコンパイラは黙って通した**」) → §5 (D1) の反例で**命題レベルで**再現する。
   ⚠ **再現先は notes 欄であって claim 欄ではない**。
2. **`## L5 (T3)` 行 4 の claim 欄**の「標的との差は『スカラー ⟹ 平面集合』1 段」 → §2 の署名 diff で再現。
   ⚠ **本 gate は同欄に訂正を 1 件出している** ⟹ 数えられるのは**訂正後の形**だけである。
3. **`## L2 (T3)` 行 6 の notes 欄の段 (2)** (基数境界による witness 空間の計算可能コンパクト性) →
   中核 3 (`IsEffectivelyCompactN (simplexN n)`) を固定 `n` で証明できたときにのみ再現。
4. **`## L2 (T3)` 行 5 の claim 欄** (一様に半計算可能な可算族の ⋂ 閉包) → 中核 7
   (`Pi01ClosedUnderIInterUniform`) の証明で再現。
5. **`## L0 (T3)` 行 5 の notes 欄**の Definition 2.4-3 (computable = 実効コンパクト ∧ computably overt) →
   2 つの片側性を別々に置いた上で、その連言を `IsComputableENNReal` の点版と突き合わせて再現。
   ⚠ **§2 の訂正 (両側 vs 片側) を織り込むこと**。

⚠⚠ **3・4・5 は「証明が付いたら再現する」型である** — **本 gate 時点で再現しているものは 1 本も無い**。

## 7. 併記 — アーク宣言の要修正点 5 件 (⚠ 本 gate は親 plan を書き換えていない)

1. **型が合っていない** — 宣言は 型 = **定義** だが、5 項目のうち 3 項目 ((L-∃)・(L-∀)・一様 Π01 の ⋂ 閉包) は
   **定理**であり、受け皿では `def _ : Prop` に駐車されている (§0-a)。⚠ **その形のまま層 3 へ載せる既定値は
   tier 5 の入口である**。
2. **「BC 側の」が事実に反する** — (β) 層に BC 由来の型は 1 つも無い (§1 反論 3)。子 plan
   [`bc-computable-region-formalization-plan.md`](bc-computable-region-formalization-plan.md) §3.1 は単位 A を
   「**BC から独立**」と書いており、**親のアーク宣言と子が食い違っている** (CLAUDE.md「conflict の際は子が SoT」)。
3. **死因語彙の不整合** — §5.3 の型表は 定義型の死因を `non-reproducing` / `inert` と定めるが、A2 の
   反証条件 (1) は既定の立場を `redundant` に置く。⚠ **本 gate は反証条件の逐語に従って `redundant` を出した**。
4. **選定理由の限定落ち** — 「§0 の Lean 側はこの層を通らないと閉じない」は**既知の散文経路に対する必要性**
   である (§4-b、N2-i)。
5. **座標づけの def 2 本が 5 項目から落ちている** (§0-c)。⚠ **これが無いと中核 3 は単位 B の witness 空間に
   当たらない**。

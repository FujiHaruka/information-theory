# docstring tidy-up plan — Mathlib スタイルへの寄せ込み（英語化含む）

**Status**: Phase 0–5 + 2.5 DONE (2026-06-22、CJK 0 / プロセス語彙 0 / full build green)。**Phase 5 DONE** (per-theorem 散文スタイル → Mathlib テンプレ、全ファミリ完遂。最終 = EPI honesty-dense light-touch `ea1490b0`)。**Phase 6 DONE** (2026-07-26、Phase 4 後に再発した先頭太字 topic ラベルの再スイープ)。**Phase 7 DONE** (2026-07-26、監査プロセスのナラティブ除去 + 陳腐化した虚偽記述の張り替え)。**Parent**: なし (standalone) /
**関連**: 規約 SoT [`rules/docstrings.md`](rules/docstrings.md) ・実測 [`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) ・honesty タグ SoT [`audit/audit-tags.md`](audit/audit-tags.md)

分割リファクタ (footprint の裾を named lemma に割る) に着手する**前に**、既存 docstring を Mathlib スタイルへ整える。
docstring が綺麗だと、後続の概念分割で切り出し単位を判断しやすくなる。

## Context

実測 ([`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) §1.4):

- **文書化率**: Mathlib は宣言の ~17–20% しか docstring を持たない (def + headline 定理が中心、補助補題は裸)。
  本プロジェクトは private 含め ~94%。= 大幅な過剰文書化。
- **プロセス語彙の混入**: docstring / module doc に `Phase A/B`・`Wall N`・`判断 #X`・`Retraction log`・`撤退ライン`
  といった**開発プロセス情報**が蓄積 ('Phase' は 187 ファイル、'撤退' 42、'判断' 28)。
  Mathlib の永続ドキュメントは数学だけを語り、control state / 決定履歴は語らない。
- **decision (2026-06-13) A**: 補助補題の docstring は **Mathlib 流に大幅に削る** (ユーザー決定)。
  現行 [`rules/docstrings.md`](rules/docstrings.md) の「補題にも推奨」と方針が変わる → 規約も改訂する。
- **decision (2026-06-13) B**: コード表面 (`.lean` の docstring / コメント) の散文を **英語へ全面移行**
  (ユーザー決定、Mathlib PR 水準が目標)。識別子は既に英語。内部の plan / handoff は作業言語として日本語のままでよい。
  → A で削る分は翻訳不要になるため、A と B は同一パスで行うのが効率的 (削る → 残る分だけ英語で書く)。

宣言内訳 (2026-06-13 実測):

| 区分 | 数 | 扱い |
|---|---|---|
| def / abbrev | 445 | **保持**して中身整理 (Mathlib も def は文書化必須) |
| structure / class / inductive | 33 | **保持** |
| theorem / lemma | 2176 | 削る候補母集団 |
| `@[entry_point]` 付き | 709 | **保持** (headline = main results) |
| `@residual` 保持 | 66 | **保持必須** (honesty 台帳) |
| `@audit:` 保持 | 644 | **保持必須** (タグだけ残し散文は削れる) |

## Approach

**2 つの結合したワークストリームを、ファイル単位で 1 パスにまとめて適用する** (全ファイルを 2 回走査しない):

1. **module doc 整形** — [`rules/docstrings.md`](rules/docstrings.md) のテンプレ順序へ寄せ、
   プロセス語彙の散文を除去/移設し、`## Main statements` に headline を捕捉する。
2. **宣言 docstring の選別削除** — 下記 keep/strip ルールで、内部補助補題の**散文**を削る。
   honesty タグは残す。名前が事実を語れない補題は削らず最小 1 行に留める (name-adequacy gate)。
3. **生き残る散文の英語化** — 上 2 つで残った docstring / コメントの散文を**英語で書く** (既存日本語は翻訳)。
   A (削除) で大半の日本語が消えるので、翻訳対象は keep 集合 (def + headline + module doc + load-bearing コメント) に絞られる。

**順序**: 規約改訂 (新ポリシー = SoT 化) → 1 ファミリで pilot して削除ルールと「整形後の形」を較正
→ ファミリ単位で展開 → 検証 (text-only ゆえ compile 影響なし。最後に full build + tag 数保存 + pre-commit)。

**なぜこの形か**:

- module doc と宣言 docstring は結合している。補助補題の散文を削ると、その意味の置き場所は module doc の
  `## Main statements` / `## Main definitions` に移る。だから「削る」と「main statements 捕捉」は同一パスで行う。
- 純 doc 編集は**コメントだけ**を触るので elaboration に影響しない (= compile が壊れない)。
  rename を**この pass では行わない**ことで text-only を保ち、ファミリ並列 / 高速化を可能にする。
- 「2 割まで下げる」という数値は**追わない**。タグ保持 (644+66) と entry_point (709) と def (478) を残すため、
  文書化率は構造的に Mathlib より高く着地する。意味ルール (補助補題の散文を削る) で削る。

## Keep / Strip ルール (新ポリシー)

宣言 docstring の**散文**は、宣言が次のいずれかなら **keep**(整える):

- `def` / `abbrev` / `structure` / `class` / `inductive` (Mathlib docBlame と同じ: 定義は文書化必須)
- `@[entry_point]` 付き / module doc の `## Main statements` に挙がる headline 定理
- `@residual(...)` / `@audit:*` を持つ宣言 — ただし**散文は削ってタグだけ残してよい**
  (例: audit:ok の補助補題は散文を削り `/-- @audit:ok(...) -/` だけ残す)

上記以外 (= 内部の補助 theorem / lemma) は散文を **strip**。ただし **name-adequacy gate**:

- 削る前に「Mathlib 流の名前が statement を語れているか」を確認する。
- 語れている → 散文を削る (docstring ごと削除、タグが無ければ)。
- 語れていない → **削らず最小 1 行**の数学的 docstring に縮める + rename 候補として別リストに記録
  (rename は dep graph に波及するので**この pass ではやらない**。後続の分割/命名 pass で処理)。

**Pilot (Stein.lean) で確定した運用ルール**:

- **新規 docstring を追加しない**。原則は「削る → 残る分だけ英語化」。docstring の無い
  `@[entry_point]` / headline は、名前が結論を語っていれば **bare のまま放置してよい**。
  文書化の追加は別 pass。
- **minimize の運用**: 結論の等式/不等式の「形 (RHS)」を英語 1 行で残す。証明戦略・出自
  (「AEP の N 分布化」等)・plan/inventory 参照・loogle 件数は削除する。
- **セクション見出し `/-! ### ... -/`**: 数学的ロードマップ (何をどう構成するか) だけを英語で書く。
  証明の詳細算術・多行導出は書かない (それは証明本体の `--` コメントが持つ)。Phase 番号・「未着手」・
  judgment 番号は除去する。
- 個別宣言の「なぜこの statement 形を選んだか」という**構造的理由**は、その宣言の docstring 内に
  英語で残してよい (プロセス語彙ではない)。

## Hard invariants (違反したら DEFECT)

1. **honesty タグを落とさない**: `@residual` (66) / `@audit:` (644) の総数は pass 前後で**不変**。
   タグを含む docstring を丸ごと削除してはならない (散文だけ削り、タグ行を残す)。
   pre-commit hook が「sorry に @residual 無し」を BLOCK するので安全網はあるが、依存しない。
2. **main results を捨てない**: 補助補題の散文を削る前に、その意味が名前 or module doc で拾えることを確認。
3. **compile を壊さない**: コメント以外を触らない。最後に full `lake build` で 0 error 確認。
4. **rename しない (この pass では)**: 名前が不十分でも削るのでなく最小 1 行に留める。

## Phases

### Phase 0 — 規約改訂 (SoT 化) ✅ DONE (2026-06-13)

- [`rules/docstrings.md`](rules/docstrings.md) を新ポリシーへ改訂: 「補題にも推奨」→
  「def/structure/class/inductive + headline(@[entry_point]) + タグ保持宣言のみ文書化。
  内部補助補題は名前で語らせ裸 (name-adequacy gate)」。
- module doc のプロセス語彙除去ルールを明文化 (Phase/Wall/判断/Retraction/撤退 の散文は plan/handoff へ移すか削除。
  数学的・構造的な設計判断のみ `## Implementation notes` に残す)。
- linter 方針の追記 (docBlame 非対称: def には docstring 要求、theorem/lemma には要求しない。
  pre-commit / plan_lint への弱い enforcement は分割リファクタ後に判断 → 本 pass では linter 化しない)。

### Phase 1 — pilot (1〜2 ファイルで較正) ✅ DONE (2026-06-13)

- 概念集中型で Phase 散文を持つ代表ファイル (例 `Shannon/Stein.lean`) と、
  プロセス語彙が濃いファイル 1 本で両ワークストリームを適用。
- diff をレビューし、keep/strip 境界・name-adequacy gate の運用・整形後の module doc 形を確定。
- pilot で確定した「before/after の見本」をこの plan か rules/docstrings.md に 1 例貼る。

**Pilot メトリクス**: 対象 `Shannon/Stein.lean` — 98 insertions / 144 deletions、
CJK 55→0、`lake env lean` clean、honesty tag 0→0、`@[entry_point]` 10→10。

#### Pilot 見本 (before/after)

**module doc** — JP の Phase スコープ宣言 + 「## 構成」「## 設計メモ」を、Mathlib テンプレへ:

```lean
-- before
/-!
# Stein の補題 — Phase A〜B (achievability) スコープ

仮説検定の最適 type-II error が KL の指数で減衰することを示す Stein の補題
(Cover-Thomas Theorem 11.8.3) のうち、**lower bound (achievability)** までを
スコープとする。Phase C (converse, upper bound) と Phase D (統合形 `Tendsto`)
は本ファイルでは未着手。

## 構成
* **Phase A** — log-likelihood ratio plumbing: ...
* **Phase B** — Stein lower bound: ...

## 設計メモ
* AEP plumbing の **2 分布化** で 70〜80% の補題を再利用。...
-/

-- after
/-!
# Stein's lemma

Stein's lemma for binary hypothesis testing (Cover–Thomas, Theorem 11.8.3): the optimal
type-II error of an `n`-sample test ... decays exponentially in `n` at the rate of the
Kullback–Leibler divergence `klDiv P Q`. ...

## Main definitions
* `llrPmf P Q` — the alphabet-side log-likelihood ratio `log P{x} − log Q{x}`. ...

## Main statements
* `stein_strong_law` — the empirical mean of the log-likelihood ratio converges ...

## Implementation notes
* The log-likelihood-ratio plumbing is obtained as the two-distribution specialization of
  the AEP development, which lets most ... lemmas be reused rather than reproved. ...
-/
```

**strip 例** — 名前が結論を語る補題は docstring ごと削除:

```lean
-- before
/-- Composition lift of `IdentDistrib` to `logLikelihoodRatio`. -/
lemma identDistrib_logLikelihoodRatio ...

-- after  (docstring 削除、bare)
lemma identDistrib_logLikelihoodRatio ...
```

**minimize 例** — 4 行の textbook argument 散文 → 結論形のみ 1 行:

```lean
-- before
/-- **Q-side mass bound**: `Q^n(T_ε^n) ≤ exp(-n · (klDiv - ε))`.

The textbook Stein-typicality argument: on `T_ε^n`, the empirical LR is at least
`klDiv - ε`, so each block ... Summing over `T` ... gives the
bound. AEP `typicalSet_card_le` の Q 測度版。 -/
theorem steinTypicalSet_Q_prob_le ...

-- after
/-- The `Qⁿ`-mass of the Stein-typical set is at most `exp(-n · ((klDiv P Q).toReal − ε))`. -/
theorem steinTypicalSet_Q_prob_le ...
```

### Phase 2 — ファミリ単位ロールアウト ✅ DONE (2026-06-14, `7b35db0`..`40f59e9`)

全ファミリを module doc 整形 / 補助補題散文削除 / 英語化の text-only 1 パスで整形。波ごとに
tag 数 (@residual/@audit) を before/after 照合・保存確認、`lake env lean` sorry-warning 0。

### Phase 3 — 検証 / メトリクス ✅ DONE (2026-06-14, `62077c70`)

full `lake build InformationTheory` 3471 jobs green・全ツリー CJK 0・pre-commit 0 BLOCK を機械確認。

### Phase 2.5 — 過去波プロセス語彙スイープ ✅ DONE (2026-06-14, `db18279d`)

CJK→0 済ファイルに系統的残存していたプロセス語彙 (Phase ラベル / wave・judgment / retreat-slug /
dated closure metadata) を 100 ファイル・12 バッチで除去。全タグ verbatim 保存・code byte-identical・
full build green を機械確認。

### Phase 4 — bold-label 剥がし + 末尾ピリオド ✅ DONE (2026-06-22)

[`rules/docstrings.md`](rules/docstrings.md) 乖離表の残り 2 軸（太字 topic ラベル始まり / 末尾ピリオド無し）を
能動一括移行で解消。topic ラベル / 太字センテンスは完全文の地の文へ、識別子の太字は backtick 化、
inline named-theorem 言及の太字のみ残す。同時に末尾ピリオド付与・太字巻き込み honesty タグの unwrap も処理。

- **残存太字は named-theorem 固有名の inline prose 参照 4 件のみ**（2026-06-22 時点の実測。Phase 5 が named theorem に太字を*付与*し、その後 topic ラベルが再発 → Phase 6）:
  `Shannon/LZ78/ZivEntropyBridge.lean:16` / `Shannon/LZ78/EmpiricalEntropyMean.lean:28` の `**log-sum inequality**`、
  `Shannon/BirkhoffErgodic.lean:14` の `**Birkhoff individual ergodic theorem**`、
  `Shannon/Hoeffding/Lagrange.lean:19` の `**Intermediate Value Theorem**`。
- **検証**: `lake build InformationTheory` green (exit 0, 3503 jobs) / `@residual`/`@audit:` タグ行数不変 (base 557 = HEAD 557, verbatim) / invariant (proof 不変・compile 不変・rename なし・新規 docstring 追加なし) 充足。

### Phase 5 — per-theorem 散文スタイルのギャップ埋め ✅ DONE (2026-06-22)

**完遂サマリ**: pilot=Sanov `ec88258` で 4 軸を確定後、全ファミリを逐次 dispatch (並列度 1) で整形。Shannon 直下 singles 全 + ChannelCoding/RateDistortion/LZ78/Sanov/Chernoff/Stein/Fano/Pinsker/Cramér/MaxEntropy/Huffman/Han/AEP/Hoeffding/ParallelGaussian/SlepianWolf/WynerZiv/SMB/FisherInfo/AWGN/**EPI**。各バッチ検証3点 (タグ数不変・comment-strip 後 code byte-identical・`lake env lean` clean)。新規 sorry/@residual 0 ゆえ honesty audit 不要。最終ファミリ **EPI (55 files / 287 tags / 97 entry_points)** は honesty-dense (Stam/Blachman/de Bruijn の predicate + wall + 既存 module References) ゆえ最 light-touch: 唯一の honesty-clean な教科書名 headline `entropyPowerExt_add_ge_unconditional` (@audit:ok unconditional capstone) のみ `**entropy power inequality**` 太字化 `ea1490b0`、Stam/Blachman の predicate・bridge・producer・conditional scaffold・wall justification narrative は全 verbatim 据え置き (= 方針通りの正しい結果)。

Phase 0–4 で **密度・プロセス語彙・太字 topic ラベル・英語化** を片付けた。Phase 5 は残る軸 = 「**主定理 docstring が定理をどう説明するか**」を Mathlib の per-theorem テンプレートへ寄せる ([`mathlib-conventions-gap.md`](mathlib-conventions-gap.md) §5)。Mathlib 19 件 + KL/KraftMcMillan の逐語観察で確定したテンプレート: **`**太字の定理名**` (+ variant 句) + 命題 (+ 任意で See also / 設計注記)**、証明レシピ・メタは載せない。

#### Approach

§5.2 の乖離 4 軸を、Phase 2 と同じく **ファミリ単位 text-only 1 パス** にまとめて適用する (module doc と宣言 docstring は結合しているので別走査しない)。Phase 4 までの **Hard invariants 4 点 (タグ保存 / main results 不落 / compile 不変 / no rename) をそのまま継承**。逐次 subagent dispatch (並列度 1、Phase 2.5/4 と同じ。5h limit 回避)。

**1 点だけ Phase 4 と逆向き**: 5a は太字を**足す**。ただし対象は**教科書名のある定理に限る** (`docstring 規約` item 5「named theorem は太字」に沿う)。Phase 4 が剥がしたのは `**topic ラベル**:` の太字で、別物 (定理名太字 ≠ topic ラベル太字)。5b/5c/5d は従来どおり散文を**削る/退避**方向。

#### サブストリーム (確定方針込み)

**5a — named theorem を `**Name**:` 太字開始へ + 引用を References 集約** (#1, #5)
- 対象: **教科書名のある** entry_point/headline 定理 (Fano / Sanov / Cramér / Chernoff / Stein / Shannon-Hartley / Pinsker / Huffman optimality / AEP / Brascamp-Lieb / Loomis-Whitney / Birkhoff / EPI / Kraft-McMillan / DPI 等)。名前を持たない定理 (`entropyPower_pos`, `wzMarginalXY_add` 等) は平文命題のまま (Mathlib も無名定理は太字にしない)。
- 形: `Sanov A form (Cover-Thomas 11.1.4): <formula>` → `**Sanov's theorem**: <formula>` とし、**引用は file 先頭 module doc の `## References` へ移設** ([Q1 決定] full Mathlib)。1 ファイル内の同名定理は太字名を共有し variant 句で区別 (`, achievability` / `, Tendsto form`)。
- バッククォート数式始まり (~18%) は「(太字名 +) 英語命題文、数式は述部へ」に直す (#5)。
- **bare な named-theorem には docstring を新規追加しない** (pilot ルール継承)。太字化は既存 docstring の書き換えのみ。bare のものは後続 pass 用に別リスト記録。
- References 形式: `docs/references.bib` は**未作成** → 当面は散文引用 (`* Cover, T. M., & Thomas, J. A. (2006). *Elements of Information Theory*. Theorem 11.1.4`)。BibTeX `[Key]` 化は別 pass (bib 整備とセット)。既存 `## References` は 5 ファイルのみ。

**5b — 証明レシピ・依存補題散文の退避** (#2)
- 対象: docstring 内の `follows from` / `obtained by` / `Computation:` / `Proved by` / `by chaining` / `via` (entry_point docstring の ~17% ≈ 103 件 + 内部補題)。grep は **docstring スコープに限定**して抽出 (proof 本体コメントの ` via ` 等を巻き込まない。素の全文 grep は 980 で過大)。
- [Q2 決定] **粒度別**: **headline 定理** = 証明方針を module doc の `## Implementation notes` / proof-idea 段落へ**移設して保全** (KraftMcMillan が「counting argument」を module doc に置く形)。**内部補助補題** = レシピごと**削除** (git に履歴)。
- **保持**: 「なぜこの仮定が要るか」の設計理由 (`Real.sInf_empty = 0` 規約・`Real.log 0 = 0` 規約・`2^x` を避け `Real.exp`) は §5.3 通り Mathlib の `Note that …` と同種で**残す**。レシピ (どう示すか) と設計理由 (なぜこの形か) を取り違えない。

**5c — プロセス/メタ散文の撤去** (#3) — タグは残し散文だけ落とす
- 役割語り (`drives the saturating case`, `principal hand-off from the interior layer`, `pass-through style as relay_cutset_outer_bound`, `kept as a named primitive for symmetry` 等 ~45 箇所) を撤去。proof-architecture narrative であって構造的設計理由ではない (Phase 2.5 の延長)。
- 監査ログ型 docstring (commit ハッシュ + 日付 + `#print axioms` 結果 + `independent honesty audit` の長文、17 ファイル) を撤去。`AWGN/Main.lean` の honesty-audit 注記が筆頭。
- `(not in Mathlib)` 不在注記 5 箇所を撤去 (不在の事実は plan/handoff へ)。
- **厳守**: `@residual(...)` / `@audit:*` の**タグ行**は verbatim 保存 (Hard invariant #1)。退避は「`@`-prefixed タグ行は残し、それ以外の散文を選別削除」を最初に明示。

**5d — クロスリファレンス慣用の整理** (#4, 機会主義的)
- sibling 補題への言及が証明レシピ散文に埋もれている分を、`See also \`X\`` / `Superseded by \`X\`` の独立句に切り出す (Mathlib 慣用)。5a–5c のついでに拾う、独立波は立てない。

#### 順序・検証

1. **pilot 1 ファミリ** (教科書名定理が密で 5a–5c が全部出る `Sanov` か `Chernoff` 1 本) で 4 軸を適用、before/after 見本を確定 (Phase 1 と同じ運用)。
2. **ファミリ単位ロールアウト** — 逐次 dispatch。各波で `@residual`/`@audit` タグ総数を before/after 照合。
3. **検証** — text-only ゆえ compile 影響なし。波ごと `lake env lean`、最後に full `lake build` 0 error + タグ数不変 + pre-commit 0 BLOCK。honesty audit 不要 (新規 sorry/@residual を導入しない)。

#### Pilot 確定 (Sanov、commit `ec88258`) — before/after 見本

ロールアウトはこの形に揃える。5a の太字名は**教科書名のある entry_point/headline に限る** (sub-result ラベルは平文据え置き)。

```
-- 5a 太字名 + 引用を module doc References へ
- /-- Sanov A form (Cover-Thomas Theorem 11.1.4): `Q^n(T(P)) ≤ exp(-n · klDivSumForm P Q)`. -/
+ /-- **Sanov's theorem** (A form): `Q^n(T(P)) ≤ exp(-n · klDivSumForm P Q)`. -/

-- 5a variant 句 + 5d See also (corollary 言及を独立句へ)
- /-- Sanov A form, `klDiv` exponent (corollary of `typeClass_Qn_le`): … -/
+ /-- **Sanov's theorem** (A form), `klDiv` exponent: …
+
+ See also `typeClass_Qn_le`. -/

-- 5b headline = レシピ削除 (証明方針は module doc Implementation notes に既存保全)
- /-- Sanov LDP equality form …  Proof: `sanov_ldp_upper_bound` gives … close via … -/
+ /-- **Sanov's theorem** (LDP, equality form): …
+ for the minimizer `P` whose rounded type sequence eventually lies in `E n`. -/

-- module doc 末尾に共通 References (references.bib 未作成 → 散文)
+ ## References
+ * T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006. Theorem 11.1.4.
```

確定した運用判断 (ロールアウトで踏襲): module doc の `## Implementation notes` にある proof-method 句 (`extracted by sandwiching`, `closes via …`) は **Q2 通り残す** (proof-idea の正規の置き場)。撤去するのは per-theorem docstring 側のレシピのみ。「ratio form: …」等の等価形提示は設計理由扱いで**残す** (レシピではない)。module doc header の `Cover-Thomas Theorem X.Y` framing 行は据え置き (per-theorem 引用のみ References へ寄せる)。

### Phase 6 — 先頭太字 topic ラベルの再スイープ ✅ DONE (2026-07-26)

Phase 4 の後に書かれた宣言が `**topic ラベル**:` 始まりを再導入していた分を除去。5 バッチ逐次 dispatch
(`df40c66d` BroadcastChannel / `5145b9f1` MultipleAccess / `51a49ea1` TimeBandLimiting+ShannonHartley /
`ef65ae25` LZ78+WynerZiv+RateDistortion / `1b3ceef5` 残り) で 48 ファイル。作業項目コード
(`S3a` / `P3b` / `Leaf` / `Deliverable`) を数学記述へ言い換えた分も同パスで処理。

- 太字始まりの総数 275 (111 ファイル) → 90 (69 ファイル)。**残る 90 は全て named theorem**
  ([`rules/docstrings.md`](rules/docstrings.md) item 5 が明示的に許す形) で、topic ラベルの残件は無い。
- **検証**: 触れた全ファイル `lake env lean` 0 error / `@residual`・`@audit:*` タグは verbatim 保存。
- **教訓 (Phase 4 と同じ機構の再現)**: 一括移行は一度きりでは効かない。規約を知らない新規宣言が
  太字ラベルを書き戻す。再計測コマンドは**総数**しか返さず違反数ではない (named theorem か否かは
  機械判定できない) ので、compliant な床 90 を超えた分だけをラベル単位で仕分ける。

### Phase 7 — 監査ナラティブ除去スイープ ✅ DONE (2026-07-26)

コード面の永続記録 (`.lean` の docstring / コメント) から**監査プロセスのナラティブ**を除去し、
陳腐化して虚偽に化けた記述を実態へ張り替えるスイープ。根拠は [`rules/docstrings.md`](rules/docstrings.md)
L66/L80 (プロセス語彙を永続記録に書かない)、境界は同 L71 (honesty タグは残す)。

9 バッチ (A–C は前セッション、D–I は今セッション) を `style-auditor` へ逐次 dispatch。commit (新しい順):
`87c2fee7`(最終7本)/`59a87046`(H,9)/`dc48df5c`(G,10)/`3cfe549a`(F,12)/`af05d50f`(E,10)/
`473c204d`+`b19cce56`(D,8)/`e1124ce3`(C)/`1ee17dc2`/`bd71db59`(B)/`1a94159f`/`983b700c`(A)。

**完了判定** (機械実測、`87c2fee7` 時点):

| マーカー | before | after |
|---|---|---|
| 日付 `2026-xx-xx` | 38 | **1** (`ParallelGaussian/PerCoord.lean:687` の `@[deprecated (since := ...)]`、Lean 必須構文で対象外) |
| 監査プロセス実況 (`Audited <date>`/`independent audit`/`auditor`) | — | **0** |
| `Phase`/`Leg` 開発ステージラベル | — | **0** |
| `wall:<slug>` 参照 | 69 | **0** |

再計測 (完了状態を散文にキャッシュせず毎回引く):

```
rg -o '202[0-9]-[0-9]{2}-[0-9]{2}' InformationTheory --glob '*.lean' | wc -l
rg -o '[Aa]udited [0-9]|independent (honesty )?audit|audit PASS|auditor' InformationTheory --glob '*.lean' | wc -l
rg -o '\bPhase [0-9A-Z]|\bLeg [A-Z][0-9]?\b|\bleg [0-9]' InformationTheory --glob '*.lean' | wc -l
rg -o 'wall:[a-z0-9-]+' InformationTheory --glob '*.lean' | wc -l
```

`genuine`/`Genuine` は 549 → 216 (102 ファイル、`rg -oi genuine` 実測)。ゼロ化は意図的に見送り: 残るのは
load-bearing/vacuity/junk value との明示的対比を伴う実質語で、消すと論証の根拠が落ちる。判断基準は
「その語を消して意味が変わるなら残す、変わらないなら消す」。

全バッチで `lake env lean` 0 error・コメント除去後の文字列完全一致 (code byte-identical)・
`gen_readme_table.ts --check` PASS を維持。新規 sorry/@residual を導入しないため honesty audit 不要。

**得られた知見**: 除去より張り替えの方が価値が高かった。監査ナラティブは単に冗長だったのでなく、
陳腐化して**虚偽に化けていた**。実在しない参照先 (`IsLZ78ConverseCodingLowerBound` /
`stamToEPIBridge_holds` / `AwgnCapacityConverseMaxent` 等 9 件) と、事実と逆向きの記述
(`DeBruijnConclusion` の「Genuine residual remaining」節は当該定理が実際は `@audit:ok`、
`h_max_ent` を「body の sorry」とする記述は実際は明示引数、`tsum_prolateEigenvalues_eq` を「未解決」
とする記述 5 箇所は `#print axioms` 確認で sorryAx-free) が見つかった。永続記録に書かれた「他の宣言の
状態」はキャッシュであり無効化されない — CLAUDE.md「Plan / docs hygiene」の re-derive > cache は
plan だけでなくコードの docstring にも同じ強さで効く。docstring に書いてよいのは自身の数学的内容で
あって、他所の進捗ではない。

**手順上の教訓**: 陳腐化した事実を 1 つ見つけたら、同じ事実に依存する記述をプロジェクト全体から `rg`
で洗う (取りこぼしが繰り返し見つかった)。タグ不変性は行 grep でなくコメント除去後の文字列完全一致で
検証する (複数行 docstring の継続行は行 grep で拾えず、1 箇所取りこぼした)。監査タグの括弧内は
style-auditor に触らせない (根拠か冗長語かの区別自体が honesty 判定であり、初回バッチで書き換えさせ
非空虚性根拠 2 件を喪失した)。

**残タスク** (scope 外として切り出し、TaskList 登録済): #25 旧フラットモジュール名の docstring 散文参照
(`docs/rules/module-structure.md` 別タスク③、件数未計測)。#26 宣言名に含まれるプロセス語彙/`genuine`
のリネーム検討 (`awgn_capacity_closed_form_genuine` は README 定理表掲載 headline のため波及大)。

## DoD

- proof done / proof 内容は**不変** (これは純 doc tidy であって proof には触れない)。
- 上記 Hard invariants 4 点を全て満たす。
- 新ポリシーが [`rules/docstrings.md`](rules/docstrings.md) に反映済 (= SoT 更新済)。
- honesty audit は**不要** (新規 sorry/@residual を導入しないため)。タグ数保存で代替検証。

## Risks & mitigations

| リスク | 緩和 |
|---|---|
| 散文削除で hard-won な理解を喪失 | name-adequacy gate (名前が語れない補題は削らず最小化)。git 履歴が全文保持。pilot で較正。 |
| honesty タグを巻き込んで削除 | invariant #1 (タグ数保存照合) + pre-commit BLOCK の二重網。 |
| プロセス散文と正当な Implementation note の誤判定 | 数学的/構造的(型クラス選択・simp 正規形・定義形の理由)は残す。開発履歴(Phase 順序・Retraction・撤退・判断番号)のみ削る。 |
| 並列編集で main がドリフト | ファミリ単位でファイル所有分離。text-only ゆえ衝突は git index のみ → 逐次 commit。 |
| 英語翻訳で数学的意味がずれる | 識別子は不変 (元から英語)。pilot で対訳の語彙・トーンを確定。Mathlib の同領域 docstring を範に。レビュー必須。 |

## 知見 / 教訓

- **実 sorry の権威的判定は `lake env lean` の sorry-warning であって grep ではない**。baseline の実 sorry 計数
  (`rg ':= by sorry'`) は散文中のバッククォート言及を拾って**過大計上**していた (InfiniteVariance / AWGN の「1 本」は実体なし)。

## Decision log

- 2026-06-13: rename はこの pass のスコープ外 (text-only 維持 + dep 波及回避)。名前不十分は最小 1 行 + 別リスト記録に留める。
- 2026-06-13: pilot (Stein.lean) で運用確定 — 新規 docstring は追加しない / minimize は結論形のみ残す / セクション見出しは数学ロードマップのみ (Keep/Strip ルール節に反映済)。
- 2026-06-22: Phase 5 立案 (per-theorem 散文スタイル、§5)。[Q1] 引用は module doc `## References` へ集約 (full Mathlib)。[Q2] 証明レシピは headline = module doc proof-idea へ移設保全 / 内部補助補題 = 削除。5a の太字付与は教科書名定理限定で Phase 4 の逆行ではない (定理名太字 ≠ topic ラベル太字)。
- 2026-06-14: Phase 2.5 完遂。過去波 100 ファイルを 12 バッチ逐次 dispatch で整形、tree-wide プロセス語彙 0 / 全タグ verbatim 保存 / code byte-identical / full build green。初回 `\bPhase\b` grep が 66 本だったが、Phase トークンを含まない plan-ref/dev-slug 群 (L-*/T-codes/roadmap-M) が追加で表面化し計 100 本に拡大。L-* slug は predicate 命名なら実名へ言い換え・純ラベルは除去。

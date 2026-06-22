# docstring tidy-up plan — Mathlib スタイルへの寄せ込み（英語化含む）

**Status**: Phase 0–4 + 2.5 DONE (2026-06-22、CJK 0 / プロセス語彙 0 / 太字 named-theorem 4 件のみ / full build green)。**Parent**: なし (standalone) /
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
   プロセス語彙の散文を除去/移設し、`## Main results` に headline を捕捉する。
2. **宣言 docstring の選別削除** — 下記 keep/strip ルールで、内部補助補題の**散文**を削る。
   honesty タグは残す。名前が事実を語れない補題は削らず最小 1 行に留める (name-adequacy gate)。
3. **生き残る散文の英語化** — 上 2 つで残った docstring / コメントの散文を**英語で書く** (既存日本語は翻訳)。
   A (削除) で大半の日本語が消えるので、翻訳対象は keep 集合 (def + headline + module doc + load-bearing コメント) に絞られる。

**順序**: 規約改訂 (新ポリシー = SoT 化) → 1 ファミリで pilot して削除ルールと「整形後の形」を較正
→ ファミリ単位で展開 → 検証 (text-only ゆえ compile 影響なし。最後に full build + tag 数保存 + pre-commit)。

**なぜこの形か**:

- module doc と宣言 docstring は結合している。補助補題の散文を削ると、その意味の置き場所は module doc の
  `## Main results` / `## Main definitions` に移る。だから「削る」と「main results 捕捉」は同一パスで行う。
- 純 doc 編集は**コメントだけ**を触るので elaboration に影響しない (= compile が壊れない)。
  rename を**この pass では行わない**ことで text-only を保ち、ファミリ並列 / 高速化を可能にする。
- 「2 割まで下げる」という数値は**追わない**。タグ保持 (644+66) と entry_point (709) と def (478) を残すため、
  文書化率は構造的に Mathlib より高く着地する。意味ルール (補助補題の散文を削る) で削る。

## Keep / Strip ルール (新ポリシー)

宣言 docstring の**散文**は、宣言が次のいずれかなら **keep**(整える):

- `def` / `abbrev` / `structure` / `class` / `inductive` (Mathlib docBlame と同じ: 定義は文書化必須)
- `@[entry_point]` 付き / module doc の `## Main results` に挙がる headline 定理
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

### Phase 2 — ファミリ単位ロールアウト ✅ DONE (2026-06-14)

ファミリ単位で 3 ワークストリーム (module doc 整形 / 補助補題散文の削除 / 生き残る散文の英語化) を
text-only 1 パスで適用。各波で tag 数 (@residual/@audit) を before/after 照合し保存確認。完了波:

- 波1 (12 families) `7b35db0` / 波2a (ChannelCoding/Huffman/ParallelGaussian/RateDistortion 他 + Shannon 直下) `ed4440d` / FisherInfo 13 本 `f49b8cb`。
- 波2b — EPI/AWGN 残部 + 英語プロセス語彙クリーンアップ (CJK 1633→0):
  EPI/Unconditional 7 本 `e7ba761` / EPI 機械エリア 17 本 (Case1/G2/Blachman/Conv) `d9a0516` /
  EPI/InfiniteVariance+Stam 10 本 `75e8de7` / AWGN 14 本 + Asymptotic `7ce0f7a` /
  英語プロセス語彙 11 本 (Phase/plan-ref/Wall narrative → 数学ロードマップ化) `40f59e9`。

honesty: 波2b で触れた全ファイルは `lake env lean` で sorry-warning 0、編集は comment-strip 後
code byte-identical。宣言直付け @residual/@audit タグは保存、tag slug は verbatim。

### Phase 3 — 検証 / メトリクス ✅ DONE (2026-06-14)

全 check pass (機械照合済):

- full `lake build InformationTheory` = **3471 jobs green (exit 0)**。pre-commit 0 BLOCK。
- **全ツリー CJK = 0 ファイル** (`rg -l '[ぁ-んァ-ヶ一-龠]' --glob '*.lean' InformationTheory` 空) =
  コードベース全体の英語化完了。
- 陳腐 scope 主張 (未着手 / スコープ / TODO) = 0。
- 波2b の英語プロセス語彙 (Phase / plan-ref / Wall) = docstring / 見出しで 0
  (残るのは honesty タグ slug 内の `@residual(plan:...)` / `@audit:closed-by-successor(...)` のみ、保存必須)。
- tag grep 総数の減少 (residual / audit) は全て prose-ref / dated-audit-narrative 除去で、宣言タグの脱落ではない。
- 文書化率は副指標扱いで数値は追わない (plan 既定どおり。タグ 644+66 / entry_point 709 / def 478 保持で構造的に Mathlib より高く着地)。

### Phase 2.5 — 過去波プロセス語彙スイープ ✅ DONE (2026-06-14)

英語プロセス語彙が CJK→0 済の過去波ファイルにも系統的に残存していた分を全て除去。
**100 ファイルを 12 バッチ (opus subagent, 並列度1 の逐次 dispatch) で整形**:

- 第1群 (`\bPhase\b` 66 本): ChannelCoding 8 / Hoeffding 8 / Shannon直下 13 / Cramer 4 /
  SMB+Sanov+LZ78 9 / EPI+FisherInfo+RateDistortion 8 / Probability+小family 10 / singles 6。
- 第2群 (Phase トークン無し・初回 grep 漏れ、plan-ref/wave/judgment/parked/dated 24 本)。
- dev-slug 残部 (retreat-line `L-*` / task-code `T-*` / roadmap M-stage 14 本):
  predicate を命名する `L-EPI3`/`L-SH1-3`/`L-C2` は実 predicate 名へ言い換え、純 decomposition ラベルは除去。

除去対象: Phase ラベル / plan-file 参照 / wave・seed・judgment log / Wall narrative / retraction 経緯 /
parked dev-status / dated closure metadata (`As of 2026`, axiom kernel, `0 sorry / 0 residual` 状態言明) /
retreat-line・task-code・roadmap-stage slug。保持: 全 `@residual`/`@audit` タグ (散文参照含む verbatim)・
構造的 honesty 推論 (load-bearing 判定理由 / regularity precondition / 実 residual 記述 / 補題間 delegation)。

完了判定 (全て機械照合済): 全 100 ファイル **code byte-identical** (block/line コメント除去後 HEAD と diff) /
**全タグ数 HEAD→work 不変** / `lake env lean` clean / tree-wide で散文プロセス語彙 0
(`Phase`/`-plan`/`judgment`/`wave`/`T-code`/`L-slug`/`roadmap M`/`parked-status`/`dated` = 0、
残る `scope-out` 3 は `@audit:closed-by-successor` タグの正当な根拠散文) / CJK 0 / **full `lake build` 3471 jobs green**。
honesty audit 不要 (新規 sorry/@residual を導入しないため。タグ数保存で代替検証)。

### Phase 4 — bold-label 剥がし + 末尾ピリオド ✅ DONE (2026-06-22)

[`rules/docstrings.md`](rules/docstrings.md) 乖離表の残り 2 軸（太字 topic ラベル始まり / 末尾ピリオド無し）を
能動一括移行で解消。topic ラベル / 太字センテンスは完全文の地の文へ、識別子の太字は backtick 化、
inline named-theorem 言及の太字のみ残す。同時に末尾ピリオド付与・太字巻き込み honesty タグの unwrap も処理。

- **残存太字は named-theorem 固有名の inline prose 参照 4 件のみ**（規約上 KEEP で正）:
  `Shannon/LZ78/ZivEntropyBridge.lean:16` / `Shannon/LZ78/EmpiricalEntropyMean.lean:28` の `**log-sum inequality**`、
  `Shannon/BirkhoffErgodic.lean:14` の `**Birkhoff individual ergodic theorem**`、
  `Shannon/Hoeffding/Lagrange.lean:19` の `**Intermediate Value Theorem**`。
- **検証**: `lake build InformationTheory` green (exit 0, 3503 jobs) / `@residual`/`@audit:` タグ行数不変 (base 557 = HEAD 557, verbatim) / invariant (proof 不変・compile 不変・rename なし・新規 docstring 追加なし) 充足。

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
- 2026-06-14: Phase 2.5 完遂。過去波 100 ファイルを 12 バッチ逐次 dispatch で整形、tree-wide プロセス語彙 0 / 全タグ verbatim 保存 / code byte-identical / full build green。初回 `\bPhase\b` grep が 66 本だったが、Phase トークンを含まない plan-ref/dev-slug 群 (L-*/T-codes/roadmap-M) が追加で表面化し計 100 本に拡大。L-* slug は predicate 命名なら実名へ言い換え・純ラベルは除去。

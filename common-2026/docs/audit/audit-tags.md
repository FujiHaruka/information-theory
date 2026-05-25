# Audit tags — code-as-source-of-truth 規約

honesty audit の状態 (genuine 完成 / 残課題 / 移行履歴) を **コード内に構造化マーカーで埋め込む** ことで、`rg` が単一の source of truth になる。snapshot 文書ではなく、コード自身が「現状どうなっているか」を答える。

## SoT 階層

1. **`sorry`** — primary residual marker。compiler-visible。「ここはまだ証明していない」を一語で表現する正直な道具。
2. **`@residual(<class>:<slug>)`** — 当該 `sorry` の分類補助。docstring または近接コメント。
3. **`@audit:*`** — bookkeeping (audit pass 済 / 別 plan に移管 / 後続版に置換済) 専用。残課題マーカーではない。

実装中に詰まったら **`sorry` + `@residual` で抜ける**。仮説束 (`*Hypothesis` predicate で結論型と同等の核を抱えさせる) や `:True` slot で `sorry` を回避するのは禁止 → CLAUDE.md「検証の誠実性」。

## Honesty 階層 (high → low)

honesty audit が評価する「正直さ」の階層。auditor の verdict 序列 + 実装側の選好順位はこの順で決まる。**一番 honest なのは `sorry`** — コンパイラ可視 + 「ごめんね」と明示している、隠蔽しようがない正直な未完成マーカー。

| Tier | 形態 | 含意 |
|---|---|---|
| **1** | `@audit:ok` (0 sorry / 0 @residual、auditor pass) | proof done、最高 honest |
| **2** | `sorry` + `@residual(<class>:<slug>)` | type-check done、新規実装の唯一の honest 撤退口 |
| **3** | bookkeeping (`@audit:superseded-by(slug)` / `@audit:retract-candidate(reason)`) | honest: 履歴 record / 削除候補。残課題マーカーではなく audit pass / 履歴のための metadata |
| **4** ⚠ | **legacy** `@audit:suspect(plan)` / `@audit:staged(wall)` / `@audit:defer(plan)` / `@audit:closed-by-successor(slug)` / 散文 `🟢ʰ` | 旧方針で「honest 残課題」として許容されていた load-bearing hypothesis / predicate bundling / 重複 closure 追跡形態。**新方針では defect 寄り** — tier 2 (`@residual(plan:<slug>)` 等) に書換待ち (移行レシピは下記)。auditor は発見しても即時 alert せず、incidental migration を推奨する程度の severity |
| **5** | `@audit:defect(*)` / 仮説型 ≡ 結論 (`:= h` 循環) / `:True` slot / 退化定義悪用 / name laundering / mathlib wall misuse | 真の honesty defect、即修正必要 |

**重要な含意**:

- **tier 2 (sorry + @residual) は tier 4 (suspect/staged) より strictly honest**。旧方針で「honest 名前付き仮説で抜く」と書かれていた撤退口は tier 4 で、新方針ではより上位の tier 2 に置き換える。
- **tier 4 (legacy) は無期限放置を意味しない**。新規実装で tier 4 declarations を touch するときに incidental に tier 2 へ migrate する (移行レシピ → 本ファイル下部 + [[sorry-based-migration]])。
- **auditor の verdict**: tier 5 を見つけたら即 rewrite recommend (commit revert)。tier 4 を見つけたら incidental migration recommend (緊急性低)。tier 2 の `@residual` 分類検証が主たる仕事。
- **実装側の選好**: 詰まったら必ず tier 2 を選ぶ。tier 4 を新規作成するのは禁止 (CLAUDE.md「検証の誠実性」)。

## 動機

- snapshot 文書 (defect-101 report 等) は **書いた瞬間から陳腐化** する。defect 数が変わっても文書は更新されない。
- 散文表現 (`🟢ʰ`, `(未着手)`, "NOT a discharge", "load-bearing hypothesis") が併存していると **集計不能** + 表現ゆれで grep 信頼度が落ちる。
- 監査で発見した新規 issue を「次セッションのタスク」に保管するのではなく、**発見した場所 (= 当該 docstring)** に埋め込めば、タスクリストが肥大化しない。

## 語彙

### `@residual(<class>:<slug>)` — 残課題分類 (sorry に併走)

各 `sorry` には対応する `@residual(...)` タグを 1 つ持たせる。

| Class | 意味 | Slug 規約 | 例 |
|---|---|---|---|
| `plan` | 別 plan で closure 予定 | plan filename stem (no `.md`) | `@residual(plan:epi-stam-closure)` |
| `wall` | Mathlib に未整備の壁。長期残課題 | wall name (下記 register) | `@residual(wall:stam)`、`@residual(wall:n-dim-gaussian-aep)` |
| `defect` | 旧 defect の fix 待ち残置 (signature は honest 化済、body だけ `sorry`) | defect kind (下記語彙) | `@residual(defect:circular)` |

#### Wall name register

`@residual(wall:<name>)` の `<name>` は以下から選ぶ。新規追加時は本 register に直接追記 (divergence 防止: 「stam」と「stam-inequality」が併存しないように)。

| Wall name | 意味 | 関連 textbook 節 |
|---|---|---|
| `stam` | Stam の不等式 (Blachman score-of-convolution identity)、Fisher 情報の畳み込み | Ch.17 EPI |
| `csiszar` | Csiszár projection 系の Mathlib 未整備部 | Ch.11 |
| `n-dim-gaussian-aep` | n 次元 Gaussian 上の AEP / typicality | Ch.9 AWGN |
| `sphere-volume` | 高次元球の体積 + thin shell concentration | Ch.9 AWGN |
| `continuous-aep` | 連続分布上の典型集合 / AEP の Mathlib 不在部 | Ch.9 |
| `nyquist-2w-dof` | 帯域制限信号の 2W サンプル/秒 (prolate-spheroidal 次元定理) | Ch.9 Shannon-Hartley |
| `multivariate-mi` | 連続 `mutualInfo_pi_eq_sum` (多変量 MI 加法性) | Ch.9 ParallelGaussian |
| `joint-typicality-multi` | 多変数 joint typicality / Fano | Ch.15 MAC/BC/Relay |
| `epi-n-dim` | 多次元 EPI / n-dim Prékopa-Leindler の slice 解析的 readiness | Ch.17 BM |
| `uniform-max-entropy-on-convex-body` | 凸体上 uniform 分布 = max entropy の characterization (n-dim) | Ch.17.9.4 BM |
| `bm-additive-convex-body` | 凸体の Brunn-Minkowski 加法形 `vol(A) + vol(B) ≤ vol(A + B)` | Ch.17.9 BM |
| `fourier` | Fourier 解析の Mathlib 不在部 (帯域制限 / sinc 完全性等) | Ch.9 Shannon-Hartley |

新規 wall を追加する時は: (1) loogle で 0件確認 (本当に Mathlib 不在か)、(2) 既存 register に類似がないか確認、(3) 本表に直接追記してコミット。

#### 提案中 wall (Proposed — 後続セッションで promote 判断)

以下の wall 候補は Round 2 sweep (2026-05-25) で識別されたが、各 plan のデフォルト方針
「plan-slug で揃え、wall 化は後続 PR」に従い register 追加は留保。後続 family sweep で
shared sorry 補題化の必要が浮上したら本表から上の正式 register に格上げ。

| 候補 wall name | 由来 plan | promote trigger 条件 |
|---|---|---|
| `relay-block-markov-aep` | `relay-sorry-migration-plan` | Relay block-Markov + sliding-window decoder の shared sorry 補題化が必要になったとき |
| `relay-cf-wz-binning` | `relay-sorry-migration-plan` + `wyner-ziv-discharge-moonshot-plan` | Relay CF と WynerZiv binning を 1 補題で共有したいとき |
| `csiszar-sum-conditional` | `relay-sorry-migration-plan` | 既存 `csiszar` (projection) と区別された conditional sum identity 系補題が複数 family で再出現したとき |
| `n-dim-prekopa-leindler` | `brunn-minkowski-sorry-migration-plan` + `prekopa-leindler-induction-plan` | n-dim PL Fubini induction を shared sorry 化したいとき (現状 BM closure plan が 1D PL hyp を honest hyp で保持中) |
| `bm-convex-body-sqrt` | `brunn-minkowski-sorry-migration-plan` + `brunn-minkowski-closure-plan` | 凸体 BM sqrt 形 `volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)` を BM 外の family が参照するようになったとき |
| `lz78-combinatorial-core` | `lz78-sorry-migration-plan` | Cover-Thomas Lemma 13.5.5 distinct-phrase 核を LZ77 / 他 universal coding family が参照するとき |
| `lz78-aseventual-ziv` | `lz78-sorry-migration-plan` + `lz78-aseventual-achievability-plan` | a.s.-eventual Ziv inequality (`limsup (c·log₂ c / n) ≤ H₂`) を LZ78 外が参照するとき |

promote 判定基準: (1) 該当 declaration が shared sorry 補題として 2+ family で再利用される、
または (2) `plan:<slug>` 集約より wall 化のほうが closure 計画と整合する。両条件いずれかが
満たされたタイミングで上記行を Wall name register 本表に移し、当該 declaration の
`@residual` を `@residual(plan:<slug>)` から `@residual(wall:<name>)` に書換。

**Round 3 escalate #4 — `bm-convex-body-sqrt` promote 再判定 (2026-05-26)**: BM Wave 6
で隣接 wall 2 件 (`uniform-max-entropy-on-convex-body` + `bm-additive-convex-body`、
commit `fe28966`) を正式 register 入りさせた折に本候補も再評価したが、現状 consumer
は `BrunnMinkowskiClosure.lean` 1 file 内 docstring 言及 4 件のみ
(`rg 'bm-convex-body-sqrt' Common2026/` で in-file 限定)、active
`@residual(wall:bm-convex-body-sqrt)` は **0 件** (load-bearing
`IsBMEntropyPowerVolumeHyp` predicate が closure plan §G で honest hyp として保持中、
sqrt 形 sorry はまだ書かれていない)。`cramer-sorry-migration-plan.md:722` での言及も
「同型の trigger 条件あり」という meta 比較で、Cramer family が sqrt 形を直接参照する
構造ではない。trigger 条件 (2+ family 参照 or 1 family 複数 file 参照) **不達**、Round 4
持ち越し。次回 trigger 候補: EPI route (`brunn-minkowski-from-epi-discharge-plan`) または
n-dim PL route (`prekopa-leindler-induction-plan`) で sqrt 形 sorry を新規導入したとき
(closure plan が委任先として両 plan を明示、`BrunnMinkowskiClosure.lean:548`)。

**隣接 wall との semantic 区別** (Wave 6 で正式 register 入りした 2 件 vs 本候補):

- `bm-additive-convex-body` (Wave 6 promote): 凸体の Brunn-Minkowski **加法形**
  `vol(A) + vol(B) ≤ vol(A + B)` — 体積の plain な和形、1 次元類比。
- `uniform-max-entropy-on-convex-body` (Wave 6 promote): 凸体上 **uniform 分布 = max
  entropy** の characterization (n-dim) — uniform measure の microstate count
  特徴づけ、entropy 側の statement。
- `bm-convex-body-sqrt` (本候補、保留): 凸体 BM の **sqrt 形**
  `volAB^(1/n) ≥ volA^(1/n) + volB^(1/n)` — Cover-Thomas 17.9.4 で entropy power
  Brunn-Minkowski に持ち上げる橋。加法形より strong (additive form は sqrt form の
  弱形)、entropy power lifting に直接乗る形。3 件は **互いに非重複**: 加法形 ⇐ sqrt 形
  (Minkowski 不等式 / Hölder 経由)、uniform max entropy は分布特徴づけで対象が違う。

#### Defect kind 語彙

`@residual(defect:<kind>)` の `<kind>`:

| Kind | 由来 defect | 典型例 |
|---|---|---|
| `circular` | 仮説型 ≡ 結論型 で body が `:= h` (旧 `@audit:defect(circular)`) | WynerZiv `wyner_ziv_achievability_rate` |
| `prop-true` | `:True` slot に実 residual を隠す (旧 `@audit:defect(prop-true)`) | (旧 6 件、移行済) |
| `launder` | name laundering (`*_discharged` / `*_full` / `_bridge` 等で完成偽装、旧 `@audit:defect(launder)`) | LZ78 `def IsSMBToLZ78ConverseChainBridge := IsLZ78ConverseChainHyp` (literal alias) |
| `degenerate` | 退化定義悪用 (predicate 自身は FALSE ではないが、vacuous shape / operational discard で意味を空にしている、旧 `@audit:defect(degenerate)`) | MAC/BC `bc_random_codebook_markov_of_ensemble` (本体は genuine averaging だが `obtain ⟨_C₀, _hC₀⟩` で operational witness を discard、constructor だけ満たす) |
| `false-statement` | mathlib_wall_misuse / 実は偽の statement | (旧 EPI/DeBruijn 系) |
| `false-hypothesis` | **仮説 (predicate) 自身が機械検証可能に FALSE** (反例構成済 or refutation 補題あり); 当該 wrapper の含意は vacuously-true | Huffman `EqualizingPermHypothesis` / `MergedHuffmanAuxIdentHypothesis`; LZ78 `IsLZ78ZivCombinatorialCoreOverhead` (反例 `n=16, Pₙ=1, c=5` あり、`not_isLZ78ZivCombinatorialCoreOverhead` で refutation 済) |

**`degenerate` vs `false-hypothesis` の使い分け** (Round 2 LZ78 L-MIG-3 由来の clarification):

- 「predicate が機械検証可能に FALSE」(反例構成 / refutation 補題が in-tree 存在) → **`false-hypothesis`** を使う
- 「predicate 自身は FALSE ではないが、operational witness が discard される / vacuous shape で意味を空にしている」 → **`degenerate`** を使う
- 両方該当する境界例 (predicate FALSE かつ意味も空) → `false-hypothesis` を優先 (より精確な根本原因)

新規 kind を追加する場合も本表に追記する。

**運用上の位置付け**: `@residual(defect:<kind>)` および対応する `@audit:defect(<kind>)` は次の 2 用途で使う。

1. **旧 `@audit:defect(*)` の sorry-based 後継** として既存 defect を移行するマーカー (本ファイル下部「Deprecated」表)。
2. **`def` / `Prop := ...` RHS / `inductive` constructor 等 `sorry` を書けない箇所での暫定撤退口**。`sorry` は proof body にしか書けないため、signature 自体が詰まったときは以下の順で対処する:
   - **第一選択 — 定義書換** (CLAUDE.md「Mathlib-shape-driven Definitions」)。textbook の formulation を結論形に合わせて再定義 → 性質を別 `theorem` で述べる → body `sorry` + `@residual(<class>:<slug>)` という basic route に持ち込めるなら、それが正解。shared sorry 補題化 (本ファイル下部「共有 Mathlib 壁」) も同種の手法。
   - **第二選択 (暫定)** — 当該セッションで定義書換が無理 (循環構造解消に上流再設計必要 / signature 改変の影響範囲が大 / vacuously-true wrapper として acknowledged 等) な場合は signature を defect 形のまま残し、docstring に `@audit:defect(<kind>)` + `@audit:retract-candidate(<reason>)` または `@audit:closed-by-successor(<plan-slug>)` を併記する。これは **後で第一選択に migrate する暫定マーカー** であり stable な resting state ではない (honesty audit は tier 5 として detect)。

第二選択を残す場合の必須条件 2 点: (a) docstring に「なぜ第一選択が当該セッションで無理だったか」を 1 行散文で説明、(b) 後続 plan の slug を `@audit:closed-by-successor(<plan-slug>)` で指す。両方欠けたまま tier 5 を残置するのは silent defect とほぼ同等 (auditor が即時 alert)。

**配置**: 1 sorry / 1 theorem の場合は docstring 末尾、複数 sorry の場合は各 sorry の直前行コメント。

```lean
-- パターン A: 単一 sorry → docstring に
/-- Stam の不等式の本体。
@residual(plan:epi-stam-closure) -/
theorem stamInequality_body : ... := by
  sorry

-- パターン B: 複数 sorry → 各 sorry 直前
theorem foo : ... := by
  have h1 : ... := by
    -- @residual(wall:stam)
    sorry
  have h2 : ... := by
    -- @residual(plan:foo-step-2)
    sorry
  ...
```

#### Compound syntax (Round 2 残課題 → Round 4 正式提案)

1 つの `sorry` が **複数の独立した closure 担当** (例: 別 plan + 別 wall、または 2 つの上流 plan の合流点) を持つときは、`@residual(...)` の引数に **comma-separated** で列挙してよい。Round 2 sweep で Chernoff L-MIG-4 / Cramer CLT closure 系で必要性が浮上し、Round 4 で正式登録。

**EBNF 拡張** (既存 single 形と後方互換):

```ebnf
residual-tag    = "@residual(" residual-list ")"
residual-list   = residual-item { "," residual-item }    (* NEW: comma list, 1 以上 *)
residual-item   = class ":" slug
class           = "plan" | "wall" | "defect"
slug            = kebab-identifier
```

例:

```lean
-- 単一 (既存、変更なし)
@residual(plan:awgn-mi-bridge-plan)

-- compound (NEW): 2 つの plan を AND 結合
@residual(plan:awgn-mi-bridge-plan,plan:awgn-mi-decomp-plan)

-- compound: plan + wall を AND 結合
@residual(plan:cramer-cltclosure-rewrite-recovery-plan,wall:characteristic-fn-clt)
```

**semantic (AND 限定)**: compound `@residual` は **論理 AND**。**両方** の plan / wall が closure されない限り、当該 `sorry` は解消不能。

**OR semantic は未予約**: 「どちらか一方の plan で closure 可能」を表現する `@residual-or(...)` のような alternation syntax は **現状未予約 + unsupported**。OR が必要になったタイミングで別 syntax として議題化する (本 syntax を流用しない)。

**適用シナリオ**:

1. **transitive sorry の正式表現** (Round 3 Wave 3-B Chernoff L-MIG-4 expansion で発見) — downstream wrapper が upstream の sorry + 別 plan の壁を両方 thread する場合。従来は runbook L518-521 の「タグ付与せず散文で明示」(Pattern C) で回避していたが、家族間で再帰使用が増えると散文 divergence の懸念。compound `@residual` で構造化。
2. **cross-family plumbing** — 例: Cramer の CLT closure 系で characteristic function + Stam 不等式の両方が壁、`@residual(plan:cramer-cltclosure-rewrite-recovery-plan,wall:stam)`。
3. **active consumer の bookkeeping 代替** — Round 3 BMClosure 系 escalate #2 が `closure-plan-completed` という新 reason vocab で対処したが、compound `@residual` で代替できれば retract-candidate semantic 拡張は不要だった可能性。後発の同パターン (load-bearing wall + active consumer) では compound `@residual` を先に検討すること推奨。

**transitive suffix `:transitive` との関係** (runbook L518-521): runbook 旧提案は `@residual(<class>:<slug>:transitive)` という suffix 形だったが、本 compound syntax で意図を吸収可能 (transitive 上流 sorry を closure する plan / wall を直接列挙すれば良い、suffix で「上流依存」を明示する必要は機械的には無い)。Pattern C の散文明示も引き続き許容 — `@residual` タグ無し + docstring 散文で transitive 性を表す形式は当面残す。

**registry / migration**:

- 既存 single `@residual(<class>:<slug>)` declarations はそのまま (本拡張は **strict superset**、backward-compatible)。
- 新規 compound 適用は本 vocab register 後に発生したタイミングで採用 (Round 5 以降の sweep で出現を想定)。
- 既存 sweep で散文 transitive (runbook Pattern C) として書かれているものを compound に書換える retroactive migration は **任意** (運用上の利得 = grep 集計の精度向上が見えてから判断)。

**grep recipe との整合**: compound `@residual` は既存「class 別ヒストグラム」recipe (`rg -o "@residual\([a-z]+:" ...`) では先頭 item のみカウントされる。compound 件数集計は別 pattern で行う (下記 grep recipe section 末尾 canonical pattern 追記参照)。

### `@audit:*` — bookkeeping (audit pass / 履歴 / 削除候補)

`@audit:*` は **残課題マーカーではない** (残課題は `sorry` + `@residual`)。audit 結果 + history record + 削除候補のみ。

| Tag | 意味 | Slug の中身 | sorry 持ち可? | 例 |
|---|---|---|---|---|
| `@audit:ok` | 独立 auditor が honesty pass 判定。genuine 完成 (0 sorry / 0 @residual) | (なし) | NO (定義上) | `@audit:ok` |
| `@audit:superseded-by(SLUG)` | 当該 declaration は後続版に置き換え済 (`_unconditional` 版が併存している `_of_condEntDiff` conditional 版等)。history record / API 後方互換のため削除しない | 後続 declaration / plan filename stem | YES (旧版が未完のまま残置可) | `@audit:superseded-by(wyner-ziv-convexity-unconditional)` |
| `@audit:retract-candidate(REASON)` | 削除候補。circular passthrough で honest 経路が他にあるケース等 | REASON 短文 (kebab-case、下記 Reason 語彙) | YES | `@audit:retract-candidate(circular-passthrough)` |

#### Reason 語彙 (`@audit:retract-candidate(<reason>)`)

| Reason | 意味 | 典型例 |
|---|---|---|
| `circular-passthrough` | 仮説型 ≡ 結論型の循環で、honest な代替経路が他に存在 | (新規 registration、現在使用 0 件) |
| `load-bearing-predicate` | predicate を hypothesis 形に取る load-bearing wrapper。hypothesis-form consumer 全削除済 | WynerZivBinningCovering / WynerZivPackingBody / HuffmanOptimality |
| `load-bearing-predicate-empty-consumers` | `load-bearing-predicate` の中でも consumer **0 件** であるもの (純粋削除可能) | (runbook 提案、現在使用 0 件) |
| `load-bearing-predicate-extract-only` | `load-bearing-predicate` の中でも `.field` 抽出 / bridge 経由の extract-only consumer (pass-through、load-bearing claim を inject しない) が残存しているもの | Round 3 Wave 3-D Audit-A で initial use 達成 (ChernoffPerTiltDischarge:252)、複数 family 横断 use の集計は今後継続 |
| `single-line-wrapper` | 1-line `def` で他 declaration を wrapping するだけの shim | WynerZivPackingBody |
| `name-laundering-alias` | `def X := Y` 形の literal alias で、`X` という名前にすることで discharge を偽装している (`launder` defect の def 版) | LZ78 `IsSMBToLZ78ConverseChainBridge := IsLZ78ConverseChainHyp` (`LZ78SMBSandwich.lean:307/319`) |
| `false-hypothesis` | `def` / `Prop` 自身が機械検証可能に FALSE (CLAUDE.md「sorry を書けない箇所での対処順序」第二選択)。`@audit:closed-by-successor` と併用して後継 plan を指す | LZ78 `def IsLZ78ZivCombinatorialCoreOverhead` (`LZ78ZivTreeNode.lean:403`、`not_isLZ78ZivCombinatorialCoreOverhead` で refutation 済) |
| `false-replaced-by-eps-relaxed` | false predicate を ε-relaxed 形に置き換えた場合の旧 declaration retract マーカー | ChernoffPerTiltDischarge:147 + ChernoffPerTiltSanov:148 (Round 2 commit `d83e45b`、Round 3 で usage 検出) |
| `circular-between-false-predicates` | 2 つ以上の false predicate の循環的 self-reference を解消する一方向だけを残し他方を retract | ChernoffPerTiltSanov:181 (Round 2 commit `d83e45b`) |
| `closure-plan-completed` | load-bearing wall を closure plan で acknowledged 済として bookkeeping (active consumer あり、削除候補ではない例外的用法)。tier 4 retract-candidate の semantic 拡張、後発の同パターン (LZ78 / Huffman / EPI 等) でも適用可 | BMClosure.lean L379 + L514 の active consumer 例 (escalate #2 採用判断、Round 3) |
| `superseded-by-memoryless-form` | MVP/pre-discharge 形が後続 memoryless 形に置換済 | ChannelCodingFeedback (3 件) |
| `superseded-by-full-discharge` | 完全 discharge 形が別 file で publish 済 | ChannelCodingShannonTheoremFull |

新規 reason を追加する時は本表に直接追記してコミット (divergence 防止: 「superseded」と「superseded-by」が併存しないように)。kebab-case で短く (3-4 単語以内推奨)。

### 複数タグの併用

1 つの def/theorem に `@residual` と bookkeeping `@audit:*` が同居しうる。例: 旧版で残置している wrapper:

```lean
/-- 旧 conditional 版、history record のため残置。
@residual(plan:wyner-ziv-convexity-unconditional) @audit:superseded-by(wyner-ziv-convexity-unconditional) -/
theorem wynerZivConvexity_of_condEntDiff : ... := by sorry
```

意味: 「sorry は新 unconditional 版で closure 予定 (`@residual(plan:...)`)、当該 declaration は後続版に置換済の旧 wrapper (`@audit:superseded-by`)」。

### 解除

状態が変わったら **タグ自体を編集する** (`@residual(wall:stam)` → `@audit:ok` 等)。タグは 1 declaration につき可能な限り 1 行にまとめて、`rg -A1` で前後文脈付きレビューしやすくする。

## 配置ルール

- **`@residual`**: docstring 末尾 (単一 sorry) または sorry 直前のラインコメント (複数 sorry)。
- **`@audit:*`**: 必ず docstring 内 (line comment ではなく `/-- ... -/`)。理由: docstring は declaration とライフサイクルが揃っており、grep で declaration と pair で取れる。
- **`@param` `@field` のような Lean doc-tools の予約形式とは衝突しない** (`@residual` / `@audit:` は Lean が解釈しない、純粋にコメント文字列)。

## grep レシピ

### 残課題集計

```bash
# residual 全件 (= sorry の分類済件数の下限)
rg "@residual" Common2026/ | wc -l

# class 別ヒストグラム
rg -o "@residual\([a-z]+:" Common2026/ | sort | uniq -c | sort -rn

# compound @residual (comma-separated 2 件以上) の件数集計 (Round 4 正式提案)
rg '@residual\([^)]*,[^)]*\)' Common2026/ | wc -l

# 特定壁の影響範囲

# 特定 plan の closure 待ち件数
rg "@residual\(plan:epi-stam-closure\)" Common2026/

# tag 無し sorry (= 分類漏れ、CI で検出すべき)
# ファイル単位: sorry を含むが @residual を 1 つも持たない file を列挙
for f in $(rg -l "\bsorry\b" Common2026/); do
  rg -q "@residual" "$f" || echo "$f"
done

# 行レベル: 各 sorry の直前 3 行に @residual が無いものを抽出
awk '
  FNR==1 { delete prev; pn=0 }
  /^[[:space:]]*sorry/ {
    f=0; for (i in prev) if (prev[i] ~ /@residual/) f=1
    if (!f) print FILENAME":"FNR":"$0
  }
  { prev[(pn++) % 3]=$0 }
' $(rg -l "\bsorry\b" Common2026/)
```

### 完成状態の確認

```bash
# audit pass 済件数
rg "@audit:ok" Common2026/ | wc -l

# 残課題総数 (sorry + residual の整合確認用)
rg "\bsorry\b" Common2026/ | wc -l
rg "@residual" Common2026/ | wc -l
```

### plan からの逆検索

```bash
# AWGN typicality plan は何件を抱えるか
rg "@residual\(plan:awgn-achievability-typicality\)" Common2026/

# 後続版に置き換え済の旧 declaration
rg "@audit:superseded-by\(" Common2026/

# 削除候補
rg "@audit:retract-candidate\(" Common2026/
```

### declaration-direct タグ検索の canonical pattern (Pattern D 発展形)

`@audit:suspect` / `@audit:staged` / `@audit:closed-by-successor` を **bareword** で
grep すると docstring sign-off note の **文字列リテラル参照** (例: "...の旧
`@audit:suspect` 解消...") を false positive ヒットする。declaration-direct タグの
件数集計には **必ずパーレン付き pattern** を使う:

```bash
# canonical per-family 件数集計 (推奨 one-liner)
rg -c '@audit:suspect\(|@audit:staged\(|@audit:closed-by-successor\(' Common2026/<family pattern>

# 個別タグの canonical pattern
rg '@audit:suspect\('             Common2026/
rg '@audit:staged\('              Common2026/
rg '@audit:closed-by-successor\(' Common2026/
rg '@audit:retract-candidate\('   Common2026/
```

**Pattern D 発展形の実例 4 件** (Round 3 Wave 3-A、各 planner が独立に発見):

| family / file | bareword grep ヒット | パーレン付き (実 declaration) |
|---|---:|---:|
| BMFunctional | 4 | 0 |
| WynerZiv | 2 | 0 |
| EPIL3Integration | 2 | 0 |
| InfinitePiTiltedChangeOfMeasure | 1 | 0 |

**影響範囲**: orchestrator brief の per-family 計数 drift の根本原因。
planner / inventory に渡す前段の per-family 件数集計で必ず canonical pattern
(パーレン付き) を使う。Round 3 では全 4 planner が verbatim 確認で false positive
を独立に検出したため誤伝播は防がれたが、計数のみで判断する設計だと sweep
スコープが drift する。

## 運用ルール

### 残課題の埋め方 (実装中)

実装中に dead-end に遭遇したら:

1. 仮説束 (`(h : <core claim>) → conclusion`) で核を bundling **しない**
2. signature を本来証明したい形に保つ
3. body を `sorry` にする
4. 直近 docstring/コメントに `@residual(<class>:<slug>)` を書く

これだけ。「honest 名前付き仮説」「`*Hypothesis` predicate」等の語彙は不要。

### 監査時の発見 → 即タグ付け

監査中に honesty issue を発見したら **その場で `sorry` 化 + `@residual` または `@audit:*` を docstring に書き込む**。次セッションのタスクリストやハンドオフに「これも audit したい」と書かない。

なぜ:
- タスクリストは current session 内で消える / ハンドオフは多重化して読み逃す。docstring は declaration とともに永続。
- 発見場所 = 修正場所なので、置き場が決定論的。
- レビュー時に diff で見える。

## 共有 Mathlib 壁: shared sorry 補題パターン

同じ壁 (例: Stam の不等式) を複数 file から参照する場合、**各 use site で個別に `sorry` を書かない**。1 ヶ所に「shared sorry 補題」を立て、他は normal な lemma 呼び出しで使う:

```lean
-- Common2026/Shannon/EPIStamWalls.lean
/-- Stam の不等式。Mathlib 未収録、closure 待ち。
@residual(wall:stam) -/
theorem stamInequality
    (μ : Measure ℝ) [...] :
    fisherInfo μ ≥ ... := by
  sorry

-- 各 consumer は普通に呼ぶ
theorem foo : ... := by
  have h := stamInequality μ ...
  ...
```

これにより:
- 壁 1 件 = `sorry` 1 件。重複しない。
- consumer 側 file は `@residual` を持たず、proof done 判定可能 (壁 file だけが未完成)。
- 壁 closure 時は shared 補題 1 件を埋めれば全 consumer が genuine 化。

## Deprecated (移行対象 — 別セッションで sweep)

以下のタグは旧 honesty workflow (load-bearing hyp 容認) の名残。新規導入禁止、既存は sorry-based に移行。

| 旧タグ | 移行先 |
|---|---|
| `@audit:suspect(PLAN)` (≒ 🟢ʰ load-bearing hyp) | 仮説解除 → signature を本来の形に → body `sorry` → `@residual(plan:<PLAN>)` |
| `@audit:staged(WALL)` (Mathlib 壁 predicate bundling) | predicate 削除 → 共有 sorry 補題に置換 → `@residual(wall:<WALL>)` |
| `@audit:defect(circular)` | 仮説解除 → signature 修正 → body `sorry` → `@residual(defect:circular)` |
| `@audit:defect(prop-true)` | `:True` slot 削除 → 該当 residual を sorry 化 → `@residual(defect:prop-true)` |
| `@audit:defect(launder)` | rename → signature が claim 通り → `sorry` + 適切な `@residual` |
| `@audit:defect(degenerate)` | 退化定義削除 / 修正 → `sorry` + `@residual` |
| `@audit:defer(PLAN)` | sorry が同 file にあれば `@residual(plan:<PLAN>)` に置換、無ければタグ削除 (declaration 完成) |
| `@audit:closed-by-successor(SLUG)` | wrapper 自身に sorry があれば `@residual(plan:<SLUG>)` に置換、依存先の sorry は依存先で `@residual` 管理 (sorry-based ではタグ不要、type-check 経由で transitive 追跡) |
| 散文 `🟢ʰ` / `🟢ʰ load-bearing hypothesis` | 上記 `@audit:suspect` と同じ移行 |
| 散文 `**NOT a discharge**` / `**load-bearing — NOT a discharge.**` | 同上 |
| 散文 `⚠️ OPEN — conclusion-as-hypothesis` | `@audit:defect(circular)` と同じ移行 |

`@audit:defer` / `@audit:closed-by-successor` の deprecation 理由: 新方針では sorry の closure 担当 plan は `@residual(plan:<slug>)` で一元的に表現するため、別 tag で重ねて記録する必要が無い。依存先の sorry は Lean の type-check が transitive に追跡するので、wrapper 側に「後続が closure する予定」と明示する必要も無い (依存先の `@residual` を grep すれば十分)。

### 移行レシピ (suspect 1 件あたり)

```lean
-- 旧
/-- Stam ineq 経由の EPI step.
@audit:suspect(epi-stam-closure) -/
theorem epiStep
    (hStam : StamInequalityHolds μ ν)  -- ← load-bearing hyp
    (h... : ...) :  -- 残りは regularity
    epi μ ν := by
  exact ... hStam ...

-- 新
/-- Stam ineq 経由の EPI step.
@residual(plan:epi-stam-closure) -/
theorem epiStep
    (h... : ...) :  -- regularity だけ残す
    epi μ ν := by
  sorry
```

ポイント:
- `StamInequalityHolds` のような **core を抱える predicate hypothesis を削除**
- regularity (`IsFiniteMeasure`, full-support 等) は precondition なので残す
- body は `sorry` だけ
- tag を `@residual(plan:...)` に書換

shared sorry 補題化する場合は `StamInequalityHolds` を削除した代わりに `stamInequality μ ...` を body で呼び出し、補題側に `sorry` + `@residual(wall:stam)` を集約。

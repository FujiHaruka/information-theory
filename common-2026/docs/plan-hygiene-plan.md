# プラン衛生 (判断ログ + 確定事実のとっちらかり緩和) 計画 🧹

> **Scope**: P1 (事実は再導出) + P2 (確定事実台帳) + P3 (staleness linter) + P4 (判断ログ自動圧縮) + P6 (親子プラン整合)。
> **Non-goal**: P5 (frontmatter status + archive ライフサイクル) — ユーザー deselect (2026-06-07)。P6 は P5 の親子 slice を frontmatter なし (既存 Parent ヘッダ + sub-plan テーブルのみ) で代替する。
> **由来**: 2セッション横断調査で確認した 2 問題 (プラン肥大 / セッション間重複発見)。P6 は handoff/carryon で親 DAG が stale 化する drift。詳細データはセッション履歴。

<!-- 記法は moonshot-plan-template と同じ (📋🚧✅🔄 / 取り消し線 / 判断ログ)。
     このプラン自身が「衛生」の実例なので、肥大させない (≤ 250 行を budget とする)。 -->

## 進捗

- [x] Phase 1 — 規約変更 (P1 ルール + P4 ライフサイクル反転) ✅ (CLAUDE.md「Plan / docs hygiene」節 + テンプレ2本 + compact-plan skill 反転)
- [x] Phase 2 — 確定事実台帳フォーマット + EPI seed (P2) ✅ (format → CLAUDE.md 節 / seed → `docs/shannon/epi-facts.md`)
- [x] Phase 3 — `scripts/plan_lint.ts` staleness linter (P3) ✅ (純 Deno 走査、201 plans/~11s。実証: 141 STALE / 45 SUSPECT / 44 BUDGET 検出。レポートは gitignore で再生成式)
- [x] Phase 4 — pre-commit hook に docs-plan WARN 分岐追加 (P1+P4 強制) ✅ (P1 prose / P4 予算>600行 / P4 判断ログ>10 の3 WARN 実機確認。plan_lint は ~10s で hook 非搭載=手動/CI)
- [x] Phase 5 — handoff skill に圧縮トリガー配線 (P4 自動化) ✅ (handoff やること step 2 = plan_lint → BUDGET/STALE で /compact-plan、cleanup がセッション境界で必ず走る)
- [x] Phase 6 — 親子プラン整合 (P6) ✅ (L1 doctrine: CLAUDE.md「親子プラン整合」+ テンプレ2本 / L2 pre-commit「子だけ staged で親未 staged」WARN 実機確認 / L3 plan_lint 親子グラフ: dead リンク STALE・backlink 欠落/親子 drift SUSPECT、positive test 済 / handoff・carryon に family 一括 lint + 子 SoT 解消を配線)

## ゴール / Approach

**ゴール**: プランが「制御状態 / 判断履歴 / 確定事実」の3つを混ぜて肥大・stale 化する構造を、寿命ごとに分離して機械的に抑える。

**Approach (解の全体形)**:

問題の根は「寿命の違う3種を1ファイルに同居させ、削除禁止 + 圧縮は努力目標」という現テンプレ規約そのもの。3種を次のように分離する:

1. **確定事実** → prose にキャッシュしない。機械再導出できるもの (`sorryAx-free` / sorry 有無) は都度 `#print axioms`/`rg` で引く (P1)。再導出が高コストな少数 (loogle Found 0 / 人間判断の壁) だけ、family ごとの台帳に**確信度付き**で単一源化する (P2)。
2. **判断履歴** → 決着済は削除 (git が履歴を持つので prose 二重保存は純肥大)。予算超過 or handoff 境界で自動圧縮 (P4)。
3. **制御状態** (scope/approach/next) → プラン本体に残す。これは触らない。

**設計原則**: 規約だけの対策は既に失敗 (`compact-plan` skill は存在するのに 172/187 プランが肥大)。よって**機械強制に寄せる** — 強制点は `.githooks/pre-commit` (WARN) / `scripts/plan_lint.ts` (staleness 検出) / `compact-plan` skill + テンプレ (ライフサイクル) / `handoff` skill (圧縮トリガー)。linter は「STALE 確定」を出せるのは少数の高確信ルールだけで、残りは SUSPECT 生成器であることを明示する (decl 名抽出は heuristic で誤検出する)。

**強制点マップ**:

| 緩和策 | 規約 (SoT) | 機械強制 |
|---|---|---|
| P1 事実再導出 | `CLAUDE.md` 新節 + テンプレ注記 | pre-commit WARN (prose に `sorryAx-free`/`Found 0`) |
| P2 確定事実台帳 | `CLAUDE.md` 新節 + フォーマット spec | `plan_lint.ts` が台帳行の再検証コマンドを照合 |
| P3 staleness linter | — | `scripts/plan_lint.ts` (手動/CI) + pre-commit に軽量サブセット |
| P4 判断ログ圧縮 | テンプレ + `compact-plan` skill 反転 | pre-commit WARN (予算超過) + handoff トリガー |

## Phase 1 — 規約変更 (P1 + P4 のライフサイクル反転) 📋

CLAUDE.md に新節「## Plan / docs hygiene」を追加し、テンプレ 2 本と compact-plan skill を整合させる。

- [ ] **CLAUDE.md 新節**: (a) 確定事実は prose にキャッシュせず再導出 (機械導出可なもの)。壁は `@residual(wall:slug)` にリンク、prose に「X は壁」と書かない。(b) 高コスト否定は P2 台帳へ。(c) 判断ログは決着済を削除 (git が履歴)。(d) プラン予算 (≤ 600 行 / 判断ログ ≤ 10 active entry)。
- [ ] **`docs/moonshot-plan-template.md` + `docs/subplan-template.md`**: 「判断ログは append-only」「廃止 Phase は取り消し線で残す (完全削除しない)」を**反転** — 「決着済 entry は削除 (git 参照)」「廃止 Phase は 1 行 + commit に圧縮」。完了 Phase 圧縮を努力目標から budget 規約へ。
- [ ] **`compact-plan` skill 「気をつけること」反転**: 「判断ログは ... 削除は不可」→「決着済 (採用方針が確定 / 反例で却下済 / commit 済) entry は削除可。**active な撤退ライン・判定軸・進行中 Phase の判断は残す**」。凍結 slug (L-INT-2-α 等) 不可侵は維持。

依存: なし。最初に着手 (他 Phase が参照する規約の SoT)。

## Phase 2 — 確定事実台帳 (P2) 📋

- [ ] **フォーマット spec** (CLAUDE.md 新節内): `docs/<family>/<family>-facts.md`。表の列 = `主張 | 確信度 | 再検証コマンド | last-verified (commit) | 備考`。確信度 enum = `machine` (axiom/sorry 機械検証) / `loogle-neg` (Found 0) / `human-judgment` (壁の解析的判断、**過大/過小評価しうるので低信頼として扱う**)。
- [ ] **EPI seed** (`docs/shannon/epi-facts.md`): 現状散在している事実を移行 — 各 `@residual(wall:slug)` への index、loogle Found 0 群 (Lieb-Young / Brascamp-Lieb / Rényi-Lp)、主要 decl の sorryAx 状態は「machine + 再検証コマンド」行に。**確信度を必ず記入** (誤った壁判定の伝播防止 = 今 handoff の罠への直接の対策)。
- [ ] 既存プランの top-of-file 「Wall SoT: <file:line>」ヘッダは台帳行への参照に置換 (新規発明でなく既存ヘッダの集約)。

依存: Phase 1 のルール (台帳に何を載せ何を再導出するかの線引き)。

## Phase 3 — `scripts/plan_lint.ts` staleness linter (P3) 📋

Deno + TS、`session_metrics.ts` のスタイル (`#!/usr/bin/env -S deno run -A`)。入力 = `docs/**/*-plan.md` glob。

- [ ] **抽出**: 各プランから (a) `@residual\((wall|plan|defect):slug\)` 参照、(b) `InformationTheory/.+\.lean:\d+` の file:line アンカー、(c) 進捗の `commit <hash>`、(d) backtick 内 decl 風トークン (heuristic)。
- [ ] **高確信チェック (STALE 確定)**:
  - プランが `wall:slug` に言及するが `rg "@residual\(wall:slug\)" InformationTheory/` が 0 件 → 壁は解消済なのにプランが壁扱い (= 再発見を生む誤った確定)。**最重要ルール**。
  - file:line の file が存在しない → STALE。
- [ ] **中確信チェック (SUSPECT)**:
  - file:line の行 > `wc -l` → 行ドリフト。
  - git staleness: 参照 `.lean` の last-commit-date > プランの last-commit-date → 「sync 後にコード変更、要レビュー」(P5 frontmatter なしで git 比較に置換)。
  - backtick decl がコードに `(theorem|lemma|def|...) <name>` で見つからない → SUSPECT (誤検出ありと明示)。
- [ ] **出力**: STALE / SUSPECT / OK ランク付きレポート (stdout + `--out docs/plan-staleness-report.md`)。`--hook` モード = text+rg で済む高確信チェックのみ (pre-commit 用)。
- [ ] **限界の明示**: decl 名抽出は heuristic、行ドリフトは意図したアンカーを知らない。linter は SUSPECT 生成器であり、STALE 確定は (file 消失 / 壁 slug 消失) の 2 ルールのみ。

依存: P2 台帳 (台帳行の再検証コマンド照合を追加できると尚良、ただし独立にビルド可)。

## Phase 4 — pre-commit hook に docs-plan WARN 分岐追加 (P1+P4 強制) 📋

現 hook は「docs-only コミットは即通過」。`docs/**/*-plan.md` の staged 分岐を追加 (BLOCK しない、全て WARN)。

- [ ] staged `docs/**/*-plan.md` を集める分岐を追加。
- [ ] **P1 WARN**: 追加行に `sorryAx-free` / `Found 0` / `Mathlib 不在` の prose → 「台帳/コードにリンクを (`<family>-facts.md`)」。
- [ ] **P4 WARN**: プラン全体が > 600 行、または 判断ログ entry が > 10 → 「`/compact-plan` 候補」。
- [ ] (任意) **P3 連携**: `plan_lint.ts --hook` を呼べるなら staged プランの高確信 STALE を WARN。deno 起動コストを測り、重ければ hook には載せず手動/CI のみ。

依存: Phase 1 (語彙)、Phase 2 (台帳 path)、Phase 3 (--hook モード、任意)。最後に統合。

## Phase 5 — handoff skill に圧縮トリガー配線 (P4 自動化) 📋

`compact-plan` が今は完全 user 起動 = 一生実行されない。handoff 境界で必ず走らせる。

- [ ] `handoff` skill に step 追加: handoff 書き出し前に active family のプランを `wc -l` で計測、予算超過なら `compact-plan` を起動 (or ユーザーに 1 行提案)。
- [ ] compact-plan の「handoff.md は touch しない」制約と矛盾しないこと (対象は family plan、handoff.md は別) を skill 文に明記。

依存: Phase 1 (反転済ルール) + Phase 4 (予算定義)。

## Phase 6 — 親子プラン整合 (P6) ✅

親 moonshot plan は子の状態 (DAG 本線/park、sub-plan 進捗) を *キャッシュ* で持つ。子だけ更新して親 DAG を直し忘れると、cold な次セッションが `/carryon` で親 DAG を最初に読み park 経路を本線と誤認する (handoff/carryon の典型 drift)。frontmatter を足さず (P5 deselect 尊重)、既存の子 `**Parent**:` ヘッダ + 親 sub-plan テーブルのリンク構造だけを材料に L1/L2/L3 で抑える。

- **L1 doctrine**: CLAUDE.md「Plan / docs hygiene」に「衝突時は子が SoT、親を子に合わせて直す」を明文化 (cold セッションの decision rule)。`subplan-template.md` / `moonshot-plan-template.md` の Parent ヘッダ / sub-plan テーブル注記を「親更新の同期点」に強化。
- **L2 編集時 reminder** (pre-commit, text のみ): 子 plan (Parent ヘッダ持ち) を staged にした commit に親 plan が co-staged されていなければ WARN。
- **L3 グラフ lint** (`plan_lint.ts`): 子の Parent ヘッダから親子グラフを構築し、(a) dead `*-plan.md` リンク = STALE、(b) backlink 欠落 (親が子 slug を sub-plan 参照していない) = SUSPECT、(c) 親子 drift (子の git commit が親より新しい) = SUSPECT。`docs/**/*-plan.md` のみ読むので code 全走査が不要 = 軽量。
- **handoff/carryon 配線**: 両 skill で family 一括 `plan_lint docs/<family>/*-plan.md` を走らせ、親子 SUSPECT を「親を子に合わせる」で解消してから引き継ぐ/着手する。handoff.md State に「親子整合」行を追加。

## 非ゴール / リスク

- **P5 除外**: frontmatter `status`/`owns`/`synced_at` + `docs/archive/` 自動移動はやらない (ユーザー deselect)。P3 の sync 判定は frontmatter でなく git log 比較で代替。
- **linter 誤検出**: decl 名抽出 heuristic は false positive/negative を出す。SUSPECT は「要レビュー」であって「削除せよ」ではない。STALE 確定は 2 ルールのみ。
- **凍結 slug 不可侵**: 撤退ライン slug (L-* 系) / 凍結 Phase 番号は他文書参照ありうるので compact 時も削除しない (compact-plan 既存規約を維持)。
- **過大/過小評価両方向**: 壁判定は過大評価 (実は通れる) も過小評価 (bare で真と思ったら反例) も起きる。台帳の `human-judgment` 確信度はどちらにも転びうる前提で「低信頼」明示。

## 検証

- Phase 1-2: テンプレ/skill/CLAUDE.md の整合 (互いに矛盾する規約が残っていないか rg)。
- Phase 3: `deno run -A scripts/plan_lint.ts docs/shannon/*.md` が EPI プラン群で既知の stale (壁 slug 解消済を壁扱いしている箇所) を実際に拾うか — 拾えれば linter は機能。拾えなければ抽出ルール調整。
- Phase 4: ダミーの肥大プラン commit で WARN が出るか、`SKIP_LEAN_HOOK=1` で bypass できるか。
- Phase 5: handoff 実行で予算超過プランが圧縮提案されるか。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正時。決着済は削除 (このプラン自身が P4 規約の実例)。

1. **P5 deselect (2026-06-07)**: ユーザーが P1/P2/P3/P4 を選択、P5 (frontmatter+archive) を除外。→ P3 の sync 判定を frontmatter `synced_at` でなく git log 比較に変更。
2. **P6 採用 (2026-06-07)**: P5 deselect 後も残る親子 DAG drift (handoff/carryon で park 経路を本線と誤認) を、新 frontmatter なし (既存 Parent ヘッダ + 親 sub-plan テーブルのリンクのみ) で機械検出する L1+L2+L3 を実装。親子 drift 検出は P3 の git-staleness を「親 plan vs 子 plan の commit 比較」に流用 (新マークアップ不要)。深度はユーザー選択「推奨: L1+L2+L3 フル」。

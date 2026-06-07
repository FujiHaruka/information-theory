---
name: handoff
description: 現在のセッションの状態を `.claude/handoff.md` に書き出し、次セッションで `/carryon` から再開できるようにする。ユーザーが「セッションリセット」「次のセッション用にまとめて」「ハンドオフ書いて」「/handoff」と言ったときに起動する。今やっている作業の続きを cold な未来の自分が拾えるよう、状態 + 次の一手 + 読むべきファイル を簡潔にまとめる。
---

# handoff: セッション間の引き継ぎを書く

`.claude/handoff.md` を **上書き** で書く。次セッションで `/carryon` した未来の自分が「冷えた状態でも作業を再開できる」ことが目的。

## やること

1. **状態スナップショットを集める** (並列で OK):
   - `git status` (uncommitted の有無、branch)
   - `git log --oneline -5` (直近のコミット)
   - 現在の Task list (TaskList tool で取得)
2. **active plan の hygiene チェック** (CLAUDE.md「Plan / docs hygiene」): handoff 対象 family の `*-plan.md` を **family 一括**で検査 — `deno run -A scripts/plan_lint.ts docs/<family>/*-plan.md` (親子の両端を見るため単一 plan でなく family 一括)。
   - **BUDGET** (>600 行) が出たら handoff 前に `/compact-plan <plan>` を実行 (決着済 判断ログ entry / 完了 Phase を畳む)。
   - **STALE** (壁 slug 消失 / file 消失 / dead 親子リンク) が出たら該当箇所を修正 or 削除。次セッションが誤った確定を引き継がないため。
   - **親子整合 SUSPECT** (backlink 欠落 / 親子 drift = 子が親より後に更新) が出たら、**親 DAG / sub-plan テーブルを子に合わせて直す** (子が SoT)。cold な次セッションは親 DAG を最初に読むので、ここで解消しておかないと park 経路を本線と取り違える。
   - 圧縮対象は family plan であって `.claude/handoff.md` ではない (compact-plan の不可侵制約と非競合)。cleanup をセッション境界で必ず走らせる目的 (今は user 起動依存で実行されない)。
3. **`.claude/handoff.md` を以下の形式で書く** (`Write` で上書き)
4. ユーザーには「ハンドオフ書いた」と一言だけ。長い要約は不要 (内容はファイルにある)

## handoff.md の形式

```markdown
# Handoff — <YYYY-MM-DD HH:MM>

## State

- Branch: <branch>
- Uncommitted: <"clean" or short list>
- Active phase / 作業中の文脈: <一文>
- 親子整合: <clean / 親 P と子 C が drift・子が新しい → 次セッションは親 DAG を子に合わせて直す>

## Tasks

(TaskList の出力を pending/in_progress のみ抽出。完了済みは除く)

- #N [status] subject — description (もしあれば)

## Where we are

直近で何が終わって、何が未解決か。2〜4 文。**事実だけ**書く (推測・所感は次のセクション)。

## Next step

次セッションの最初の一手。具体的に書く:
- どのファイルを開くか
- どの sorry を埋めるか / どの bash を打つか
- 既知の戦略があれば一文で

## Files to read first

未来の自分がまず開くべきファイルを優先順で 3〜5 個。各 1 行コメント:

- `path/to/file.md` — なぜ最初に読むべきか
- ...

## Load-bearing context

ファイルからは拾えないが次セッションが知っていないとハマる事項のみ。例:

- 決定したけどまだコードに反映していない方針
- 試して却下したアプローチ (再度トライ防止)
- 今セッションで判明した Mathlib の落とし穴 / バージョン依存挙動

なければこのセクションごと省略する。
```

## 書くときの原則

- **冗長にしない**。次セッションは `.claude/handoff.md` を Read するだけ — そこに全部入っているべきだが、長すぎると逆に読まれない。全体で 50 行以内が目安
- **過去のセッションのまとめは書かない**。「今日やったこと」ではなく「次に何をするか」
- **ファイルから読める情報は重複させない**。Plan の中身を貼らない、proof の状態は file 名と行番号で参照
- **絶対パスではなくプロジェクト相対パス**で書く (移植性のため)
- ユーザーへの返答は 1〜2 行。書き出した事実 + ファイルパスだけ

## トリガー

ユーザーが以下を発話したとき必ず起動:

- 「セッションリセット」「リセットします」
- 「次のセッション用に」「ハンドオフ」
- 「引き継ぎ書いて」「まとめて終わる」
- `/handoff`

`/carryon` の対になるスキル。
